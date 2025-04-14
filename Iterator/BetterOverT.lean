import Lean.Compiler.LCNF.Simp
import Lean.Compiler.LCNF.Main
import Lean.CoreM

#check ExceptT

#check ReaderT

#check EStateM

def Cont.{v, u} (β : Type v) (α : Type u) := (α → β) → β

-- instance : Monad (Cont β) where
--   pure x f := f x
--   bind x g f := x (g · f)

def Cont'.{v, u} (m : Type v → Type w) (β : Type v) (α : Type u) := (α → m β) → m β

@[always_inline, inline]
def Cont'.run [Pure m] (x : Cont' m α α) := x pure

@[always_inline, inline]
def Cont'.bindH [Monad m] (x : Cont' m β α) (f : α → Cont' m β α') : Cont' m β α'
  | h => x (f · h)

instance [Monad m] : Monad (Cont' m α) where
  pure x h := h x
  bind x f h := x (f · h)

instance [Monad m] : MonadLift m (Cont' m α) where
  monadLift x f := x >>= f

inductive USwitchT (m : Type w → Type w') : Type u → Type (max u w w' + 1) where
  | eval : ∀ {α β}, m α → (α → β) → USwitchT m β
  | pure : ∀ {α}, α → USwitchT m α
  | bind : ∀ {α β}, USwitchT m α → (α → USwitchT m β) → USwitchT m β

structure USwitchCell (m : Type w → Type w') (β α) where
  Intermediate : Type w
  monadic : Cont' m β Intermediate
  heterogeneous : Intermediate → α

instance : Monad (USwitchT m) where
  pure x := .pure x
  bind x f := x.bind f

def USwitchT.toCont [Monad m] : USwitchT m α → Cont' m β α
  | .eval x f => do return f (← x)
  | .pure x => do return x
  | .bind x f => do x.toCont >>= (fun a => (f a).toCont)

class USwitchI (α : Type u) (m : Type w → Type w') (β : Type v) where
  eval : ∀ n : Type v → Type w'',
    [Monad n] →
    (eval : ∀ {γ δ}, m γ → (γ → δ) → n δ) → -- how about calling this mapH?
    (it : α) →
    n β

@[inline]
def USwitchI.toCont [Monad m] [USwitchI α m β] (it : α) : Cont' m γ β :=
  USwitchI.eval (m := m) _ (fun x f => do return f (← x)) it

inductive IterStep (α : Type u) (β : Type v) : Type max u v where -- omitting some params that are irrelevant here
  | yield : α → β → IterStep α β
  | skip : α → IterStep α β
  | done : IterStep α β

class Iterator (α : Type u) (m : Type max u v → Type w) (β : outParam (Type v)) where
  step : α → USwitchT m (IterStep α β)

instance [Pure m] : Iterator (List α) m α where
  step it := .eval (pure ()) (fun _ => match it with
    | [] => .done
    | x :: xs => .yield xs x)

instance [Pure m] : USwitchI (List α) m (IterStep (List α) α) where
  eval _ _ _
    | [] => pure .done
    | x :: xs => pure <| .yield xs x

example : IO Nat := Cont'.run (m := IO) do
  IO.println "hi"
  return 0

set_option trace.compiler.ir.result true in
def f (l : List Nat) (init : Nat := 0) : Nat := Cont'.run (m := Id) do
  match ← USwitchI.toCont (β := IterStep (List Nat) Nat) (m := Id) l with
  | .yield it' b => return f it' (init + b)
  | .skip it' => return f it' init
  | .done => return init

  -- match ← Iterator.step (m := Id) l |>.toCont with
  -- | .yield it' b => return f it' (init + b)
  -- | .skip it' => return f it' init
  -- | .done => return init
  -- let result ← Cont'.bindH (α := ULift.{1} Nat) (f := pure ∘ ULift.down) do
  --   let mut step ← Iterator.step (m := Id) l |>.toCont
  --   return (sorry : (ULift.{1} Nat))
termination_by l
decreasing_by all_goals sorry

@[inline]
def f : USwitchT Id.{0} Nat :=
  .bind (.pure 2) (fun x => .eval x id)

def USwitchT.down {m : Type w → Type w'} [Monad m] {α : Type w} : USwitchT m α → m α
  | .eval x f => f <$> x
  | .pure x => Pure.pure x
  | .bind x f => down x >>= (fun x => down (f x))

set_option trace.compiler.ir.result true in
def g := f.down

@[specialize]
def bla (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => x + bla xs

set_option trace.compiler.ir.result true in
def blub (l : List Nat) : Nat :=
  bla (0 :: l)

class C (α : Type u) where
  f : α → α

instance : C α where
  f := id

@[inline_if_reduce]
def x {α : Type u} [C α] (l : List α) (d : α): α :=
  match l with
  | [] => d
  | y :: ys => x ys y

set_option trace.compiler.ir.result true in
def g (l : List (Nat → Nat)) : Nat :=
  x l id 5

@[specialize]
def foldlM {α β} {m} [Monad m] (l : List α) (f : β → α → m β) (init : β) : m β :=
  match l with
  | [] => pure init
  | x :: xs => do foldlM xs f (← f init x)

set_option trace.Compiler true in
def f (l : List Nat) : IO Nat :=
  let sub : ReaderT Nat IO Nat := do
    foldlM l (init := ← read) (fun acc x => do IO.println s!"{x}"; pure (acc + x))
  sub.run 5

set_option trace.compiler.ir.result true in
def f' (l : List Nat) : ReaderT Nat IO Nat :=
  let sub : ReaderT Nat IO Nat := do
    foldlM l (init := ← read) (fun acc x => do IO.println s!"{x}"; pure (acc + x))
  sub

set_option trace.Compiler.result true in
set_option compiler.small 0 in
@[noinline]
def f'' (l : List Nat) : IO Nat := do
  for i in [0:100000] do
    if i == 0 then IO.println s!"{← (f' l |>.run 5)}"
  return 0

set_option trace.compiler.ir.result true in
@[noinline]
def f''₂ (l : List Nat) : IO Nat := do
  for i in [0:100000] do
    if i == 0 then IO.println s!"{← (f' l |>.run 5)}"
  return 0

def f''' (l : List Nat) : IO Unit := do
  timeit "" <| discard <| f'' l
  timeit "" <| discard <| f''₂ l
  return ()

#eval f''' [1, 2, 3]
