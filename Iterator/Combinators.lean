/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Wrapper

section FilterMap

-- todo: more universe polymorphism
variable {m : Type max u v → Type max u v} {α : Type u} {β γ : Type v} {f : β → Option γ}

variable (α) in
structure FilterMap (f : β → Option γ) where
  inner : α

instance [Iterator α m β] [Functor m] : Iterator (FilterMap α f) m γ where
  yielded it it' b := ∃ b', f b' = some b ∧ Iterator.yielded it.inner it'.inner b'
  skipped it it' := (∃ b', f b' = none ∧ Iterator.yielded it.inner it'.inner b') ∨ Iterator.skipped it.inner it'.inner
  finished it := Iterator.finished it.inner
  step it := (match · with
    | .yield it' x h => match h' : f x with
      | none => .skip ⟨it'⟩ (.inl ⟨x, h', h⟩)
      | some y => .yield ⟨it'⟩ y ⟨x, h', h⟩
    | .skip it' h => .skip ⟨it'⟩ (.inr h)
    | .done h => .done h) <$> Iterator.step it.inner

theorem FilterMap.finiteIteratorWF_subrelation [Functor m] [Iterator α m β] :
    Subrelation
      (FiniteIteratorWF.lt (α := (FilterMap α f)))
      (InvImage FiniteIteratorWF.lt (finiteIteratorWF ∘ FilterMap.inner ∘ FiniteIteratorWF.inner)) := by
  intro x y hlt
  simp only [FiniteIteratorWF.lt, Iterator.yielded, Iterator.skipped] at hlt
  obtain ⟨b, b', h⟩ | ⟨b', h⟩ | h := hlt
  · exact Or.inl ⟨b', h.2⟩
  · exact Or.inl ⟨b', h.2⟩
  · exact Or.inr h

theorem FilterMap.productiveIteratorWF_subrelation [Functor m] [Iterator α m β] :
    Subrelation
      (ProductiveIteratorWF.lt (α := (FilterMap α (some ∘ f))))
      (InvImage ProductiveIteratorWF.lt (productiveIteratorWF ∘ FilterMap.inner ∘ ProductiveIteratorWF.inner)) := by
  intro x y hlt
  simp only [ProductiveIteratorWF.lt, Iterator.yielded, Iterator.skipped] at hlt
  obtain ⟨_, h, _⟩ | h := hlt
  · contradiction
  · exact h

instance [Functor m] [Iterator α m β] [Finite α] : Finite (FilterMap α f) where
  wf := FilterMap.finiteIteratorWF_subrelation.wf <|
    InvImage.wf (finiteIteratorWF ∘ FilterMap.inner ∘ FiniteIteratorWF.inner) Finite.wf

@[inline]
def Iter.filterMap [Iterator α m β] [Functor m] (f : β → Option γ) (it : Iter (α := α) m β) :
    Iter (α := FilterMap (Iter (α := α) m β) f) m γ :=
  toIter ⟨it⟩

@[inline]
def Iter.map [Iterator α m β] [Functor m] (f : β → γ) (it : Iter (α := α) m β) :
    Iter (α := FilterMap (Iter (α := α) m β) (some ∘ f)) m γ :=
  toIter ⟨it⟩

@[inline]
def Iter.filter [Iterator α m β] [Functor m] (f : β → Bool) (it : Iter (α := α) m β) :
    Iter (α := FilterMap (Iter (α := α) m β) (fun x => if f x then some x else none)) m β :=
  toIter ⟨it⟩

end FilterMap

section FlatMap

-- todo: more universe polymorphism
variable {m : Type u → Type u} {α α' β β' : Type u} [Iterator α m β] [Iterator α' m β'] {f : β → α'}

abbrev RawStep (α β) := IterStep α β (fun _ _ => True) (fun _ => True) True

class Iteration (m) [Monad m] (γ : Type u) where
  prop : γ → Prop
  elem : m { c // prop c }

@[inline]
def Iteration.pure {γ m} [Monad m] (c : γ) : Iteration m γ :=
  { prop c' := (c' = c), elem := Pure.pure ⟨c, rfl⟩ }

@[inline]
def Iteration.bind {γ δ m} [Monad m] (t : Iteration m γ) (f : γ → Iteration m δ) : Iteration m δ :=
  { prop d := ∃ c, (f c).prop d ∧ t.prop c, elem :=
    Bind.bind t.elem (fun c => (fun x => ⟨x.1, ⟨c.1, x.2, c.2⟩⟩) <$> (f c.1).elem) }

@[inline]
def Iteration.step {α β : Type u} [Iterator α m β] [Monad m] (it : α) : Iteration m (RawStep α β) :=
  { prop
      | .yield it' b _ => Iterator.yielded it it' b
      | .skip it' _ => Iterator.skipped it it'
      | .done _ => Iterator.finished it,
    elem := (fun step => match step with
        | .yield it' b h => ⟨.yield it' b ⟨⟩, h⟩
        | .skip it' h => ⟨.skip it' ⟨⟩, h⟩
        | .done h => ⟨.done ⟨⟩, h⟩) <$> Iterator.step it
  }

instance (m) [Monad m] : Monad (Iteration m) where
  pure := Iteration.pure
  bind := Iteration.bind

def Iteration.instIterator [Monad m] (stepFn : α → Iteration m (RawStep α β)) : Iterator α m β where
  yielded it it' b := (stepFn it).prop (.yield it' b ⟨⟩)
  skipped it it' := (stepFn it).prop (.skip it' ⟨⟩)
  finished it := (stepFn it).prop (.done ⟨⟩)
  step it := (match · with
    | ⟨.yield it' b _, h⟩ => .yield it' b h
    | ⟨.skip it' _, h⟩ => .skip it' h
    | ⟨.done _, h⟩ => .done h) <$> (stepFn it).elem

-- def ndMatch {α m β} [Iterator α m β] (it : α) (yield : α → β → Prop) (skip : α → Prop) (finish : Prop) : Prop :=
--   (∃ it' b, Iterator.yielded it it' b ∧ yield it' b) ∨
--     (∃ it', Iterator.skipped it it' ∧ skip it') ∨
--     (Iterator.finished it ∧ finish)

-- def FlatMap.rawStep_eq [Iterator α m β] [Iterator α' m β'] (it : FlatMapAux α f) (step : IterStep (FlatMapAux α f) β' (fun _ _ => True) (fun _ => True) True) : Prop :=
--   match it with
--   | { it₁, it₂ := none } =>
--     ndMatch it₁
--       (yield := fun it₁' b => (step = .skip { it₁ := it₁', it₂ := some (f b) } ⟨⟩))
--       (skip := fun it₁' => (step = .skip { it₁ := it₁', it₂ := none } ⟨⟩))
--       (finish := (step = .done ⟨⟩))
--   | { it₁, it₂ := some it₂ } =>
--     (∃ it₂' b, Iterator.yielded it₂ it₂' b ∧ step = .yield { it₁ := it₁, it₂ := some it₂' } b ⟨⟩) ∨
--       (∃ it₂', Iterator.skipped it₂ it₂' ∧ step = .skip { it₁ := it₁, it₂ := some it₂' } ⟨⟩) ∨
--       (Iterator.finished it₂ ∧ step = .skip { it₁ := it₁, it₂ := none } ⟨⟩)

-- instance [Functor m] [Iterator α m β] [Iterator α' m β'] : Iterator (FlatMapAux α f) m β' where
--   yielded it it' b := FlatMap.rawStep_eq it (.yield it' b ⟨⟩)
--     -- | { it₁, it₂ := some it₂ }, { it₁ := it₁', it₂ := some it₂' }, b => it₁ = it₁' ∧ Iterator.yielded it₂ it₂' b
--     -- | _, _, _ => False
--   skipped it it' := FlatMap.rawStep_eq it (.skip it' ⟨⟩)
--     -- | { it₁, it₂ := none }, { it₁ := it₁', it₂ := none } => Iterator.skipped it₁ it₁'
--     -- | { it₁, it₂ := none }, { it₁ := it₁', it₂ := some it₂' } => ∃ b, f b = it₂' ∧ Iterator.yielded it₁ it₁' b
--     -- | { it₁, it₂ := some it₂ }, { it₁ := it₁', it₂ := none } => it₁ = it₁' ∧ Iterator.finished it₂
--     -- | { it₁, it₂ := some it₂ }, { it₁ := it₁', it₂ := some it₂' } => it₁ = it₁' ∧ Iterator.skipped it₂ it₂'
--   finished it := FlatMap.rawStep_eq it (.done ⟨⟩)
--     -- | { it₁, it₂ := none } => Iterator.finished it₁
--     -- | _ => False
--   step
--     | { it₁, it₂ := none } =>
--       (match · with
--       | .yield it₁' b h => .skip { it₁ := it₁', it₂ := some (f b) } (.inl ⟨it₁', b, h, rfl⟩)
--       | .skip it₁' h => .skip { it₁ := it₁', it₂ := none } (.inr <| .inl ⟨it₁', h, rfl⟩)
--       | .done h => .done (.inr <| .inr ⟨h, rfl⟩)) <$> Iterator.step it₁
--     | { it₁, it₂ := some it₂ } =>
--       (match · with
--         | .yield it₂' b h => .yield { it₁ := it₁, it₂ := some it₂' } b (.inl ⟨it₂', b, h, rfl⟩)
--         | .skip it₂' h => .skip { it₁ := it₁, it₂ := some it₂' } (.inr <| .inl ⟨it₂', h, rfl⟩)
--         | .done h => .skip { it₁ := it₁, it₂ := none } (.inr <| .inr ⟨h, rfl⟩)) <$> Iterator.step it₂

structure FlatMap (α) (f : β → α') where
  it₁ : α
  it₂ : Option α'

@[inline]
def flatMapStepNone [Monad m] [Iterator α m β] [Iterator α' m β'] (it₁ : α) : Iteration m (RawStep (FlatMap α f) β') :=
  (match · with
  | .yield it₁' b _ => .skip { it₁ := it₁', it₂ := some (f b) } ⟨⟩
  | .skip it₁' _ => .skip { it₁ := it₁', it₂ := none } ⟨⟩
  | .done _ => .done ⟨⟩) <$> Iteration.step it₁

instance [Monad m] [Iterator α m β] [Iterator α' m β'] : Iterator (FlatMap α f) m β' :=
  Iteration.instIterator fun
    | { it₁, it₂ := none } => flatMapStepNone it₁
    | { it₁, it₂ := some it₂ } => do
      match ← Iteration.step it₂ with
        | .yield it₂' b _ => return .yield { it₁ := it₁, it₂ := some it₂' } b ⟨⟩
        | .skip it₂' _ => return .skip { it₁ := it₁, it₂ := some it₂' } ⟨⟩
        | .done _ => flatMapStepNone it₁

-- instance [Monad m] [Iterator α m β] [Iterator α' m β'] : Iterator (FlatMap α f) m β' where
--   step
--     | it@⟨{ it₁ := _, it₂ := none}⟩ => do
--       match ← Iterator.step it.inner with
--       | .yield it' b h => return .yield ⟨it'⟩ b h
--       | .skip it' h => return .skip ⟨it'⟩ h
--       | .done h => return .done h
--     | it@⟨{ it₁ := _, it₂ := some _ }⟩ => do
--       match ← Iterator.step it.inner with
--       | .yield it' b h => return .yield ⟨it'⟩ b h
--       | .skip it'@{ it₁ := _, it₂ := some _ } h => return .skip ⟨it'⟩ h
--       | .skip it'@{ it₁ := _, it₂ := none } h => return convertStep (← Iterator.step it')
--       | .done h => by rfl
--   where
--     @[inline]
--     convertStep : IterStep (FlatMapAux α f) .. → IterStep (FlatMap α f) ..
--       | .yield it' b h => .yield ⟨it'⟩ b h
--       | .skip it' h => .skip ⟨it'⟩ h
--       | .done h => .done h


end FlatMap
