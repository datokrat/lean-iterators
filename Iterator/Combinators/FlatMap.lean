/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.Option.Lemmas
import Iterator.Combinators.FilterMap

/-!
This file provides the `flatMap` iterator and variants of it.

To each output of some base iterator `it`, `it.flatMap f`, applies `f` to obtain an inner iterator.
The `flatMap` iterator will yield all of the outputs of such an inner iterator before making the
next step with `it`. In other words, `it` flattens the iterator of iterators obtained by mapping with `f`.

Several variants of `flatMap` are provided:

* `H` suffix: heterogeneous variant that allows switching the monad and the universes.
* `D` suffix: dependently typed mapping function
-/

-- section ULiftState

-- universe u' v u

-- variable {α : Type u} {β : Type v}
--   {m : Type (max u v) → Type (max u v)}
--   {n : Type (max u v u') → Type (max u v u')}
--   {f : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → n δ'}

-- structure IterULiftState (α : Type u) (f : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → n δ') : Type (max u u') where
--   down : α

-- @[inline]
-- def IterULiftState.up (it : α) (f : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → n δ') : IterULiftState.{u'} α f :=
--   ⟨it⟩

-- instance [Monad n] [Iterator α m β] : Iterator (IterULiftState.{u'} α f) n β where
--   yielded it it' b := Iterator.yielded m it.down it'.down b
--   skipped it it' := Iterator.skipped m it.down it'.down
--   finished it := Iterator.finished m it.down
--   step it := do
--     let s ← f ULift.up.{u'} (Iterator.step it.down)
--     return match s.down with
--     | .yield it' b h => .yield ⟨it'⟩ b h
--     | .skip it' h => .skip ⟨it'⟩ h
--     | .done h => .done h

-- def IterULiftState.downMorphism [Monad n] [Iterator α m β] :
--     IteratorMorphism (IterULiftState.{u'} α f) α where
--   mapIterator := IterULiftState.down
--   mapValue := id
--   preserves_yielded := Iff.rfl
--   preserves_skipped := Iff.rfl
--   preserves_finished := Iff.rfl

-- def Iter.uLiftState [Monad n] [Iterator α m β] (f : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → n δ') (it : Iter (α := α) m β) :
--     Iter (α := IterULiftState.{u', v, u} α f) n β :=
--   toIter ⟨it.inner⟩

-- instance [Monad n] [Iterator α m β] [Finite α] : Finite (IterULiftState.{u'} α f) :=
--   IterULiftState.downMorphism.pullbackFinite

-- end ULiftState

section FlatMap

section FlattenDef

variable {α : Type u} {β : Type v} {β' : Type w} {α₂ : Type u₂}
  {γ : Type x} {m : Type w → Type w'} {f : β → α₂}

@[ext]
structure FlatMap (α : Type w) (f : β → α₂) where
  it₁ : α
  it₂ : Option α₂

@[always_inline, inline]
def FlatMap.init (it : α) (f : β → α₂) : FlatMap α f :=
  ⟨it, none⟩

variable (m f) in
@[always_inline, inline]
def flatMapStepNone [Monad m] [Iterator α m β] [Iterator α₂ m γ] (it₁ : α) :
    IterationT m (RawStep (FlatMap α f) γ) :=
  matchStepH it₁
    (fun it₁' b => pure <| .skip ⟨it₁', some (f b)⟩ ⟨⟩)
    (fun it₁' => pure <| .skip ⟨it₁', none⟩ ⟨⟩)
    (pure <| .done ⟨⟩)

variable (m f) in
@[always_inline, inline]
def flatMapStepSome [Monad m] [Iterator α m β] [Iterator α₂ m γ] (it₁ : α) (it₂ : α₂) :
    IterationT m (RawStep (FlatMap α f) γ) :=
  matchStepH it₂
    (fun it₂' b => pure <| .yield ⟨it₁, some it₂'⟩ b ⟨⟩)
    (fun it₂' => pure <| .skip ⟨it₁, some it₂'⟩ ⟨⟩)
    (flatMapStepNone m f it₁)

-- TODO: avoid duplication of matching on it₁, which will produce bloated code
instance [Monad m] [Iterator α m β] [Iterator α₂ m γ] : SimpleIterator (FlatMap α f) m γ where
  step it := match it with
    | ⟨it₁, none⟩ => flatMapStepNone m f it₁
    | ⟨it₁, some it₂⟩ => flatMapStepSome m f it₁ it₂

end FlattenDef

section Finite

variable {α : Type u} {β : Type v} {β' : Type w} {α₂ : Type u₂}
    {γ : Type x} {γ' : Type w} {m : Type w → Type w'} {f : β → α₂}

variable (α m f) in
def rel [Monad m] [Iterator α m β] [Iterator α₂ m γ] : (FlatMap α f) → (FlatMap α f) → Prop :=
  InvImage
    (Prod.Lex
      (InvImage FiniteIteratorWF.lt (finiteIteratorWF (m := m)))
      (Option.lt (InvImage FiniteIteratorWF.lt (finiteIteratorWF (m := m)))))
    (fun it => (it.it₁, it.it₂))

theorem FlatMap.rel_of_left [Monad m] [Iterator α m β] [Iterator α₂ m γ] {it it'}
    (h : (finiteIteratorWF (m := m) it'.it₁).lt (finiteIteratorWF it.it₁)) : rel α m f it' it :=
  Prod.Lex.left _ _ h

theorem FlatMap.rel_of_right [Monad m] [Iterator α m β] [Iterator α₂ m γ] {it₁ it₂ it₂'}
    (h : (Option.lt (InvImage FiniteIteratorWF.lt (finiteIteratorWF (m := m)))) it₂' it₂) :
    rel α m f ⟨it₁, it₂'⟩ ⟨it₁, it₂⟩ :=
  Prod.Lex.right _ h

theorem descending_flattenStepNone
    [Monad m] [Iterator α m β] [Iterator α₂ m γ] {it₁ : α} {it' : FlatMap α f}
    (h : (flatMapStepNone m f it₁ |>.mapH IterStep.successor).property (some it')) :
    (finiteIteratorWF (m := m) it'.1).lt (finiteIteratorWF it₁) := by
  simp only [flatMapStepNone] at h
  have := successor_matchStepH h
  obtain ⟨it'', b, hy, h⟩ | ⟨it'', hs, h⟩ | ⟨hd, h⟩ := this
  · cases successor_skip.mp h
    exact Or.inl ⟨_, hy⟩
  · cases successor_skip.mp h
    exact Or.inr hs
  · cases successor_done.mp h

theorem descending_flattenStepSome
    [Monad m] [Iterator α m β] [Iterator α₂ m γ] {it₁ : α} {it₂ : α₂} {it' : FlatMap α f}
    (h : (flatMapStepSome m f it₁ it₂ |>.mapH IterStep.successor).property (some it')) :
    rel α m f it' ⟨it₁, it₂⟩ := by
  simp only [flatMapStepSome] at h
  obtain ⟨it', b, hy, h⟩ | ⟨it', hs, h⟩ | ⟨hd, h⟩ := successor_matchStepH h
  · cases successor_yield (α := FlatMap α f) (m := m) |>.mp h
    apply FlatMap.rel_of_right
    exact Or.inl ⟨_, hy⟩
  · cases successor_skip (α := FlatMap α f) (m := m) |>.mp h
    apply FlatMap.rel_of_right
    exact Or.inr hs
  · apply FlatMap.rel_of_left
    exact descending_flattenStepNone h

-- TODO: put this into core
theorem Option.wellFounded_lt {α} {rel : α → α → Prop} (h : WellFounded rel) : WellFounded (Option.lt rel) := by
  refine ⟨?_⟩
  intro x
  have hn : Acc (Option.lt rel) none := by
    refine Acc.intro none ?_
    intro y hyx
    cases y <;> cases hyx
  cases x
  · exact hn
  · rename_i x
    induction h.apply x
    rename_i x' h ih
    refine Acc.intro _ ?_
    intro y hyx'
    cases y
    · exact hn
    · exact ih _ hyx'

instance [Monad m] [Iterator α m β] [Iterator α₂ m γ] [Finite α m] [Finite α₂ m] :
    SimpleIterator.Finite (FlatMap α f) m where
  rel := rel α m f
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact InvImage.wf _ Finite.wf
    · exact Option.wellFounded_lt <| InvImage.wf _ Finite.wf
  subrelation {it it'} h := by
    simp only [SimpleIterator.step] at h
    split at h
    · apply FlatMap.rel_of_left
      exact descending_flattenStepNone h
    · exact descending_flattenStepSome h

end Finite

section Dependent

variable {m : Type w → Type w'}
  {β : Type v} {α : β → Type u'} {γ : Type v'}

structure SigmaIterator {β : Type v} (α : β → Type u') where
  b : β
  inner : α b

instance {β : Type w} {α : β → Type u'} [Monad m] [∀ b, Iterator (α b) m γ] :
    SimpleIterator (SigmaIterator α) m γ where
  step it := by
    exact matchStepH it.inner
      (fun it' c => pure <| .yield ⟨it.b, it'⟩ c ⟨⟩)
      (fun it' => pure <| .skip ⟨it.b, it'⟩ ⟨⟩)
      (pure <| .done ⟨⟩)

def SigmaIterator.lex (r : (b : β) → α b → α b → Prop) :
    SigmaIterator α → SigmaIterator α → Prop :=
  InvImage (PSigma.Lex emptyRelation r) (fun it => ⟨it.b, it.inner⟩)

theorem SigmaIterator.lex_of_right (r : (b : β) → α b → α b → Prop)
    {b it it'} (h : r b it it') : SigmaIterator.lex r ⟨b, it⟩ ⟨b, it'⟩ :=
  PSigma.Lex.right _ h

variable (m) in
def SigmaIterator.rel [∀ b, Iterator (α b) m γ] :
    SigmaIterator α → SigmaIterator α → Prop :=
  SigmaIterator.lex (fun _ => InvImage FiniteIteratorWF.lt (finiteIteratorWF (m := m)))

instance {β : Type w} {α : β → Type u'}
    [Monad m] [∀ b, Iterator (α b) m γ] [∀ b, Finite (α b) m] : SimpleIterator.Finite (SigmaIterator α) m where
  rel := SigmaIterator.rel m
  wf := by
    rw [SigmaIterator.rel]
    apply InvImage.wf
    refine ⟨fun ⟨b, it⟩ => ?_⟩
    apply PSigma.lexAccessible
    · exact emptyWf.wf.apply b
    · intro a
      apply InvImage.wf
      exact Finite.wf
  subrelation {it it'} h := by
    obtain ⟨_, _, hy, h⟩ | ⟨_, hs, h⟩ | ⟨hd, h⟩ := successor_matchStepH h
    · cases successor_yield.mp h
      apply SigmaIterator.lex_of_right
      exact Or.inl ⟨_, hy⟩
    · cases successor_skip.mp h
      apply SigmaIterator.lex_of_right
      exact Or.inr hs
    · cases successor_done.mp h

end Dependent

section Iter
/--
Given an iterator `it` and an iterator-valued mapping function `f`,
`it.flatMap f` is an iterator that applies `f` to each output of `it` and concatenates all of the iterators
obtained by applying `f`.
It will yield all of the outputs of the current inner inner iterator before making the
next step with `it`.

**Marble diagram:**

```text
it                 ---a    ---b     c    --d--⊥
f a                   a1-a2⊥
f b                           b1-b2 ⊥
f c                                 c1-c2⊥
f d                                        ⊥
it.flatMap         ---a1-a2---b1-b2 c1-c2  ---⊥
```

Note that it is always possible for the implementation to insert some skip steps in between.
The insertion of additional skip steps is an implementation detail and should not be relevant
for any consumer.

**Termination properties:**

* `Finite` instance: only if `it` and all of the iternal iterators are finite
* `Productive` instance: only if `it` it finite and all of the internal iterators are productive

_TODO:_ implement the `Productive` instance

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it` or an internal stream.

_TODO_: Improve this so that the cost is only incurred with each output of `it`. This should at
least work for internal iterator types that contain a computationally cheap empty iterator.
-/
@[always_inline, inline]
def Iter.flatMap {α : Type u} {β : Type v} {α₂ : Type u₂}
    {γ : Type x} {m : Type w → Type w'}
    [Monad m] [Iterator α m β] [Iterator α₂ m γ] [ComputableUnivLE.{max u u₂, w}]
    {_ : ComputableSmall.{w} α} {_ : ComputableSmall.{w} α₂}
    (f : β → Iter (α := α₂) m γ)
    (it : Iter (α := α) m β) :=
  (toIter m <| (⟨it.inner, none⟩ : FlatMap α (Iter.inner ∘ f)) : Iter m γ)

end Iter

end FlatMap
