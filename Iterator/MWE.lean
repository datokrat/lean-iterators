
variable {α : Type u} {β : Type v}

inductive IterStep (α β) (yielded : α → β → Prop) (skipped : α → Prop) (finished : Prop) where
| yield : (it : α) → (b : β) → yielded it b → IterStep α β yielded skipped finished
| skip : (a : α) → skipped a → IterStep α β yielded skipped finished
| done : finished → IterStep α β yielded skipped finished

set_option pp.all true in
def IterStep.successor {yp sp fp} : IterStep α β yp sp fp → Option α
  | .yield it _ _ => some it
  | .skip it _ => some it
  | .done _ => none

class Iterator (α : Type u) (m : outParam (Type (max u v) → Type x)) (β : outParam (Type v)) where
  yielded : α → α → β → Prop
  skipped : α → α → Prop
  finished : α → Prop
  step : (a : α) → m (IterStep α β (yielded a) (skipped a) (finished a))

section Finite

structure FiniteIteratorWF (α : Type u) [Iterator α m β] where
  inner : α

def FiniteIteratorWF.lt {α m β} [Iterator α m β] (x y : FiniteIteratorWF α) : Prop :=
  (∃ b, Iterator.yielded y.inner x.inner b) ∨ Iterator.skipped y.inner x.inner

def finiteIteratorWF {α m β} [Iterator α m β] (it : α) : FiniteIteratorWF α :=
  ⟨it⟩

class Finite (α) [Iterator α m β] : Prop where
  wf : WellFounded (FiniteIteratorWF.lt (α := α))

instance [Iterator α m β] [Finite α] : WellFoundedRelation (FiniteIteratorWF α) where
  rel := FiniteIteratorWF.lt
  wf := Finite.wf

macro_rules | `(tactic| decreasing_trivial) => `(tactic| first | exact Or.inl ⟨_, ‹_›⟩ | exact Or.inr ‹_›)

section Wrapper

structure Iter (m) (β : Type v) [Iterator α m β] where
  inner : α

@[inline]
def toIter {m} [Iterator α m β] (it : α) : Iter (α := α) m β :=
  ⟨it⟩

instance {m} [Functor m] [Iterator α m β] : Iterator (Iter (α := α) m β) m β where
  yielded it it' b := Iterator.yielded it.inner it'.inner b
  skipped it it' := Iterator.skipped it.inner it'.inner
  finished it := Iterator.finished it.inner
  step it := (match · with
    | .yield it' x h => .yield ⟨it'⟩ x h
    | .skip it' h => .skip ⟨it'⟩ h
    | .done h => .done h) <$> (Iterator.step it.inner)

instance [Functor m] [Iterator α m β] [Finite α] : Finite (Iter (α := α) m β) where
  wf := InvImage.wf (finiteIteratorWF ∘ Iter.inner ∘ FiniteIteratorWF.inner) Finite.wf

end Wrapper

section ListIterator

variable {m : Type u → Type u}

structure ListIterator (α : Type u) (m : Type u → Type u) where
  list : List α

instance [Pure m] : Iterator (ListIterator α m) m α where
  yielded it it' a := it.list = a :: it'.list
  skipped it it' := False
  finished it := it.list = []
  step
    | { list := .nil } => pure <| .done rfl
    | { list := x :: xs } => pure <| .yield { list := xs } x (by simp)

def List.iter {α} (l : List α) (m := Id) [Pure m] : Iter (α := ListIterator α m) m α :=
  toIter { list := l }

theorem test [Pure m] :
    Subrelation (FiniteIteratorWF.lt (α := ListIterator α m))
      (InvImage WellFoundedRelation.rel (ListIterator.list ∘ FiniteIteratorWF.inner)) := by
  intro x y hlt
  simp_wf
  simp only [FiniteIteratorWF.lt, Iterator.yielded, Iterator.skipped, or_false] at hlt
  cases hlt
  simp_all

instance [Pure m] : Finite (ListIterator α m) where
  wf := test.wf (InvImage.wf _ WellFoundedRelation.wf)

end ListIterator

section AbstractIteration

abbrev RawStep (α β) := IterStep α β (fun _ _ => True) (fun _ => True) True

abbrev IterStep.for {α β m} [Iterator α m β] (it : α) := IterStep α β (Iterator.yielded it) (Iterator.skipped it) (Iterator.finished it)

structure Iteration (m : Type u → Type v) (γ : Type u) where
  prop : γ → Prop
  elem : m { c // prop c }

@[inline]
def Iteration.pure {γ m} [Pure m] (c : γ) : Iteration m γ :=
  { prop c' := (c' = c), elem := Pure.pure ⟨c, sorry⟩ }

@[inline]
def Iteration.bind {γ δ m} [Monad m] (t : Iteration m γ) (f : γ → Iteration m δ) : Iteration m δ :=
  { prop d := ∃ c, (f c).prop d ∧ t.prop c,
    elem := t.elem >>= (fun c => (fun x => ⟨x.1, sorry⟩) <$> (f c.1).elem) }

@[inline]
def Iteration.map {γ δ m} [Functor m] (f : γ → δ) (t : Iteration m γ) : Iteration m δ :=
  { prop d := ∃ c, d = f c ∧ t.prop c,
    elem := (fun c => ⟨f c.1, sorry⟩) <$> t.elem }

@[inline]
def Iteration.mapH {γ : Type u} {m : Type u → Type v}
    {δ : Type u'} {n : Type u' → Type v'}
    (f : γ → δ) (mf : ∀ {γ' : Type u} {δ' : Type u'}, (γ' → δ') → m γ' → n δ')
    (t : Iteration m γ) : Iteration n δ :=
  { prop d := ∃ c, d = f c ∧ t.prop c,
    elem := mf (fun c => ⟨f c.1, sorry⟩) t.elem }

instance (m) [Pure m] : Pure (Iteration m) where
  pure := Iteration.pure

instance (m) [Functor m] : Functor (Iteration m) where
  map := Iteration.map

instance (m) [Monad m] : Monad (Iteration m) where
  pure := Iteration.pure
  bind := Iteration.bind

@[inline]
def Iteration.step {α : Type u} {β : Type v} [Iterator α m β] [Functor m] (it : α) : Iteration m (IterStep.for it) :=
  { prop := sorry,
    elem := (fun step => ⟨step, sorry⟩) <$> Iterator.step it }

@[inline]
def Iteration.instIterator [Functor m] (stepFn : α → Iteration m (RawStep α β)) : Iterator α m β where
  yielded it it' b := (stepFn it).prop (.yield it' b ⟨⟩)
  skipped it it' := (stepFn it).prop (.skip it' ⟨⟩)
  finished it := (stepFn it).prop (.done ⟨⟩)
  step it := (match · with
    | ⟨.yield it' b _, h⟩ => .yield it' b sorry
    | ⟨.skip it' _, h⟩ => .skip it' h
    | ⟨.done _, h⟩ => .done h) <$> (stepFn it).elem

@[inline]
def matchStep {α : Type u} {β : Type v} {γ : Type (max u v)} [Monad m] [Iterator α m β] (it : α)
    (yield : α → β → Iteration m γ) (skip : α → Iteration m γ) (done : Iteration m γ) := do
  match ← Iteration.step it with
  | .yield it' b _ => yield it' b
  | .skip it' _ => skip it'
  | .done _ => done

end AbstractIteration

section Combinators

structure FlatMap (α β α' : Type) [Iterator α m β] (f : β → α') where
  it₁ : α
  it₂ : Option α'

@[inline]
def stepNone {α β α' β' : Type} [Iterator α m β] [Iterator α' m β'] (f : β → α') [Monad m] (it₁ : α) {p₁ p₂ p₃} :
    m (IterStep (FlatMap α β α' f) β' p₁ p₂ p₃) := do
  match ← Iterator.step it₁ with
  | .yield it₁' it₂' _ => pure <| .skip { it₁ := it₁', it₂ := some (f it₂') } sorry
  | .skip it₁' _ => pure <| .skip { it₁ := it₁', it₂ := none } sorry
  | .done _ => pure <| .done sorry

instance {α β α' β' : Type} [Iterator α m β] [Iterator α' m β'] (f : β → α') [Monad m] : Iterator (FlatMap α β α' f) m β' where
  yielded := sorry
  skipped := sorry
  finished := sorry
  step
    | { it₁, it₂ := none } => stepNone f it₁
    | { it₁, it₂ := some it₂ } => do
      match ← Iterator.step it₂ with
      | .yield it₂' b _ => pure <| .yield { it₁ := it₁, it₂ := some it₂' } b sorry
      | .skip it₂' _ => pure <| .skip { it₁ := it₁, it₂ := some it₂' } sorry
      | .done _ => stepNone f it₁

instance {α β α' β' : Type} [Iterator α m β] [Iterator α' m β'] (f : β → α') [Monad m] : Finite (FlatMap α β α' f) where
  wf := sorry

structure FlatMap2 (α β α' : Type) [Iterator α m β] (f : β → α') where
  it₁ : α
  it₂ : Option α'

-- instance {α β α' β' : Type} [Iterator α m β] [Iterator α' m β'] (f : β → α') [Monad m] : Iterator (FlatMap2 α β α' f) m β' :=
--   Iteration.instIterator fun
--     | { it₁, it₂ := none } =>
--       matchStep it₁
--         (fun it₁' b => pure <| .skip { it₁ := it₁', it₂ := some (f b) } ⟨⟩)
--         (fun it₁' => pure <| .skip { it₁ := it₁', it₂ := none } ⟨⟩)
--         (pure <| .done ⟨⟩)
--     | { it₁, it₂ := some it₂ } =>
--       matchStep it₂
--         (fun it₂' b => pure <| .yield { it₁ := it₁, it₂ := some it₂' } b ⟨⟩)
--         (fun it₂' => pure <| .skip { it₁ := it₁, it₂ := some it₂' } ⟨⟩)
--         (matchStep it₁
--           (fun it₁' b => pure <| .skip { it₁ := it₁', it₂ := some (f b) } ⟨⟩)
--           (fun it₁' => pure <| .skip { it₁ := it₁', it₂ := none } ⟨⟩)
--           (pure <| .done ⟨⟩))

instance {α β α' β' : Type} [Iterator α m β] [Iterator α' m β'] (f : β → α') [Monad m] : Iterator (FlatMap2 α β α' f) m β' :=
  Iteration.instIterator fun
    | { it₁ := _, it₂ := none } => pure <| .done ⟨⟩
    | { it₁, it₂ := some it₂ } =>
      matchStep it₂
        (fun it₂' b => pure <| .yield { it₁ := it₁, it₂ := some it₂' } b ⟨⟩)
        (fun it₂' => pure <| .skip { it₁ := it₁, it₂ := some it₂' } ⟨⟩)
        (pure <| .done ⟨⟩)

instance {α β α' β' : Type} [Iterator α m β] [Iterator α' m β'] (f : β → α') [Monad m] : Finite (FlatMap2 α β α' f) where
  wf := sorry

end Combinators

section IR

set_option trace.compiler.ir.result true in
def testFlatMap (l : List (List Nat)) : Nat :=
  go (FlatMap2.mk (f := List.iter) l.iter none) 0
where
  @[specialize]
  go it acc :=
    match Iterator.step it with
    | .yield it' n _ => go it' (acc + n)
    | .skip it' _ => go it' acc
    | .done _ => acc
  termination_by finiteIteratorWF it

end IR
