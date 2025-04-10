def X (α : Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => Thunk (Option (X α n × α))

def X.steps : ∀ {n}, X α n → Nat → Option α
  | 0, _, _ => none
  | n + 1, it, 0 => it.get.map (·.2)
  | n + 1, it, k + 1 => it.get.bind (X.steps ·.1 k)

def X.valid : ∀ {n}, X α n → Prop
  | 0, _ => False
  | n + 1, it => it.get.elim True (X.valid ·.1)

def Raw1 (α : Type u) (n : Nat) := { it : X α n // X.valid it }

def Raw2 (α : Type u) := (n : Nat) × Raw1 α n

@[inline]
def Raw1.step : Raw1 α (n + 1) → Option (Raw1 α n × α)
  | ⟨it, h⟩ => it.get.map (fun s => ⟨⟨s.1, sorry⟩, s.2⟩)

set_option trace.compiler.ir.result true in
@[specialize]
def Raw1.fold (init : β) (f : β → α → β) : (n : Nat) → Raw1 α n → β
  | 0, it => False.elim sorry
  | n + 1, it => it.step.elim init (fun s => Raw1.fold (f init s.2) f _ s.1)

@[inline]
def Raw2.fold (init : β) (f : β → α → β) : Raw2 α → β
  | ⟨n, it⟩ => Raw1.fold init f n it

@[inline]
def List.iterX : (l : List α) → X α (l.length + 1)
  | [] => ⟨fun () => none⟩
  | x :: xs => ⟨fun () => some (List.iterX xs, x)⟩

@[inline]
def List.iter1 (l : List α) : Raw1 α (l.length + 1):= ⟨l.iterX, sorry⟩

set_option trace.compiler.ir.result true in
def test (l : List Nat) : Nat :=
  l.iter1.fold 0 (· + ·)
