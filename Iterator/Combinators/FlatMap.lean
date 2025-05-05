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

section FlatMapDef

variable {α : Type w} {β : Type v} {α₂ : Type w}
  {γ : Type x} {m : Type w → Type w'} [Iterator α m β]
  {f : (it : Iter (α := α) m β) → (out : β) → it.plausible_output out → Iter (α := α₂) m γ}

@[ext]
structure FlatMap (α : Type w) [Iterator α m β]
    (f : (it : Iter (α := α) m β) → (out : β) → it.plausible_output out → Iter (α := α₂) m γ) where
  it₁ : Iter (α := α) m β
  it₂ : Option (Iter (α := α₂) m γ)

def FlatMap.outerIter (it : Iter (α := FlatMap α f) m γ) : Iter (α := α) m β :=
  it.inner.it₁

-- @[always_inline, inline]
-- def FlatMap.init (it : α) (f : β → Iter (α := α₂) m β) : FlatMap α f :=
--   ⟨it, none⟩
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
* `Productive` instance: only if `it` is finite and all of the internal iterators are productive

_TODO:_ implement the `Productive` instance

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it` or an internal stream.

_TODO_: Improve this so that the cost is only incurred with each output of `it`. This should at
least work for internal iterator types that contain a computationally cheap empty iterator.
-/
@[always_inline, inline]
def Iter.flatMap {α : Type w} {β : Type v} {α₂ : Type w}
    {γ : Type x} {m : Type w → Type w'} [Monad m] [Iterator α m β] [Iterator α₂ m γ]
    (f : β → Iter (α := α₂) m γ) (it : Iter (α := α) m β) :=
  (toIter (⟨it, none⟩ : FlatMap α (fun _ out _ => f out)) m γ : Iter m γ)
/-
variable (m f) in
@[always_inline, inline]
def flatMapStepNone [Monad m] [Iterator α m β] [Iterator α₂ m γ] (it₁ : α) :
    IterationT m (IterStep (FlatMap α f) γ) :=
  matchStepH it₁
    (fun it₁' b => pure <| .skip ⟨it₁', some (f b)⟩)
    (fun it₁' => pure <| .skip ⟨it₁', none⟩)
    (pure <| .done)

variable (m f) in
@[always_inline, inline]
def flatMapStepSome [Monad m] [Iterator α m β] [Iterator α₂ m γ] (it₁ : α) (it₂ : α₂) :
    IterationT m (IterStep (FlatMap α f) γ) :=
  matchStepH it₂
    (fun it₂' b => pure <| .yield ⟨it₁, some it₂'⟩ b)
    (fun it₂' => pure <| .skip ⟨it₁, some it₂'⟩)
    (flatMapStepNone m f it₁) -/

inductive FlatMap.PlausibleStep [Iterator α₂ m γ] :
    (it : Iter (α := FlatMap α f) m γ) → (step : IterStep (Iter (α := FlatMap α f) m γ) γ) → Prop where
  | outerYield : ∀ {it₁ it₁' : Iter (α := α) m β} {b}, (h : it₁.plausible_step (.yield it₁' b)) →
      PlausibleStep (toIter ⟨it₁, none⟩ m γ) (.skip (toIter ⟨it₁', some (f it₁ b ⟨_, h⟩)⟩ m γ))
  | outerSkip : ∀ {it₁ it₁' : Iter (α := α) m β}, it₁.plausible_step (.skip it₁') →
      PlausibleStep (toIter ⟨it₁, none⟩ m γ) (.skip (toIter ⟨it₁', none⟩ m γ))
  | outerDone : ∀ {it₁ : Iter (α := α) m β}, it₁.plausible_step .done →
      PlausibleStep (toIter ⟨it₁, none⟩ m γ) .done
  | innerYield : ∀ {it₁ : Iter (α := α) m β} {it₂ it₂' : Iter (α := α₂) m γ} {c},
      it₂.plausible_step (.yield it₂' c) →
      PlausibleStep (toIter ⟨it₁, some it₂⟩ m γ) (.yield (toIter ⟨it₁, some it₂'⟩ m γ) c)
  | innerSkip : ∀ {it₁ : Iter (α := α) m β} {it₂ it₂' : Iter (α := α₂) m γ},
      it₂.plausible_step (.skip it₂') →
      PlausibleStep (toIter ⟨it₁, some it₂⟩ m γ) (.skip (toIter ⟨it₁, some it₂'⟩ m γ))
  | innerDone : ∀ {it₁ : Iter (α := α) m β} {it₂ : Iter (α := α₂) m γ},
      it₂.plausible_step .done →
      PlausibleStep (toIter ⟨it₁, some it₂⟩ m γ) (.skip (toIter ⟨it₁, none⟩ m γ))

instance [Iterator α₂ m γ] {it : Iter (α := FlatMap α f) m γ} :
    Small.{w} (Subtype <| FlatMap.PlausibleStep it) := sorry

instance FlatMap.instIterator [Monad m] [Iterator α₂ m γ] : Iterator (FlatMap α f) m γ where
  plausible_step := PlausibleStep
  step_small := inferInstance
  step it :=
    match it with
      | ⟨it₁, none⟩ => do
        match (← it₁.stepH).inflate with
        | .yield it₁' b h =>
            pure <| .deflate <| .skip ⟨it₁', some (f it₁ b ⟨_, h⟩)⟩ (.outerYield h)
        | .skip it₁' h =>
            pure <| .deflate <| .skip ⟨it₁', none⟩ (.outerSkip h)
        | .done h =>
            pure <| .deflate <| .done (.outerDone h)
      | ⟨it₁, some it₂⟩ => do
        match (← it₂.stepH).inflate with
        | .yield it₂' c h =>
            pure <| .deflate <| .yield ⟨it₁, some it₂'⟩ c (.innerYield h)
        | .skip it₂' h =>
            pure <| .deflate <| .skip ⟨it₁, some it₂'⟩ (.innerSkip h)
        | .done h =>
            pure <| .deflate <| .skip ⟨it₁, none⟩ (.innerDone h)

end FlatMapDef

section Finite

variable {α : Type w} {β : Type v} {α₂ : Type w}
    {γ : Type x} {m : Type w → Type w'} [Iterator α m β]
    {f : (it : Iter (α := α) m β) → (out : β) → it.plausible_output out → Iter (α := α₂) m γ}

variable (α m f) in
def rel [Monad m] [Iterator α₂ m γ] [Finite α m] [Finite α₂ m] :
    Iter (α := FlatMap α f) m γ → Iter (α := FlatMap α f) m γ → Prop :=
  InvImage
    (Prod.Lex
      (InvImage Iter.TerminationMeasures.Finite.rel Iter.finitelyManySteps)
      (Option.lt (InvImage Iter.TerminationMeasures.Finite.rel Iter.finitelyManySteps)))
    (fun it => (it.inner.it₁, it.inner.it₂))

theorem FlatMap.rel_of_left [Monad m] [Iterator α₂ m γ] [Finite α m] [Finite α₂ m] {it it'}
    (h : it'.inner.it₁.finitelyManySteps.rel it.inner.it₁.finitelyManySteps) : rel α m f it' it :=
  Prod.Lex.left _ _ h

theorem FlatMap.rel_of_right₁ [Monad m] [Iterator α₂ m γ] [Finite α m] [Finite α₂ m]
    {it₁} {it₂ it₂' : Iter (α := α₂) m γ}
    (h : (InvImage Iter.TerminationMeasures.Finite.rel Iter.finitelyManySteps) it₂' it₂) :
    rel α m f ⟨it₁, some it₂'⟩ ⟨it₁, some it₂⟩ := by
  refine Prod.Lex.right _ h

theorem FlatMap.rel_of_right₂ [Monad m] [Iterator α₂ m γ] [Finite α m] [Finite α₂ m]
    {it₁} {it₂ : Iter (α := α₂) m γ} :
    rel α m f ⟨it₁, none⟩ ⟨it₁, some it₂⟩ :=
  Prod.Lex.right _ True.intro

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

instance [Monad m] [Iterator α₂ m γ] [Finite α m] [Finite α₂ m] :
    FinitenessRelation (FlatMap α f) m (β := γ) where
  rel := rel α m f
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact InvImage.wf _ WellFoundedRelation.wf
    · exact Option.wellFounded_lt <| InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case outerYield =>
      cases h
      apply FlatMap.rel_of_left
      exact Iter.TerminationMeasures.Finite.rel_of_yield ‹_›
    case outerSkip =>
      cases h
      apply FlatMap.rel_of_left
      exact Iter.TerminationMeasures.Finite.rel_of_skip ‹_›
    case outerDone =>
      cases h
    case innerYield =>
      cases h
      apply FlatMap.rel_of_right₁
      exact Iter.TerminationMeasures.Finite.rel_of_yield ‹_›
    case innerSkip =>
      cases h
      apply FlatMap.rel_of_right₁
      exact Iter.TerminationMeasures.Finite.rel_of_skip ‹_›
    case innerDone =>
      cases h
      apply FlatMap.rel_of_right₂

instance FlatMap.instIteratorToArray [Monad m] [Iterator α₂ m γ] [Finite α m] [Finite α₂ m] :
    IteratorToArray (FlatMap α f) m :=
  .defaultImplementation

instance FlatMap.instIteratorFor [Monad m] [Monad n] [MonadLiftT m n] [Iterator α₂ m γ] :
    IteratorFor (FlatMap α f) m n :=
  .defaultImplementation

end Finite

section Dependent

variable {m : Type w → Type w'}
  {β : Type v} {α : β → Type w} {γ : Type v'}

structure SigmaIterator {β : Type v} (α : β → Type w) (m : Type w → Type w') (γ : Type x) where
  small : Small.{w} β := by infer_instance
  b : USquash.{w} β
  inner : Iter (α := α b.inflate) m γ

inductive SigmaIterator.PlausibleStep [∀ b, Iterator (α b) m γ]
    (it : Iter (α := SigmaIterator α m γ) m γ) : (step : IterStep (Iter (α := SigmaIterator α m γ) m γ) γ) → Prop where
  | yield : ∀ {it' : Iter (α := α (it.inner.b.inflate (small := _))) m γ} {out : γ},
      it.inner.inner.plausible_step (.yield it' out) → PlausibleStep it (.yield (toIter ⟨it.inner.small, it.inner.b, it'⟩ m γ) out)
  | skip : ∀ {it' : Iter (α := α (it.inner.b.inflate (small := _))) m γ},
      it.inner.inner.plausible_step (.skip it') → PlausibleStep it (.skip (toIter ⟨it.inner.small, it.inner.b, it'⟩ m γ))
  | done : it.inner.inner.plausible_step .done → PlausibleStep it .done

instance [∀ b, Iterator (α b) m γ] {it : Iter (α := SigmaIterator α m γ) m γ} :
    Small.{w} (Subtype <| SigmaIterator.PlausibleStep it) := sorry

instance SigmaIterator.instIterator {β : Type v} {α : β → Type w} [Monad m] [∀ b, Iterator (α b) m γ] :
    Iterator (SigmaIterator α m γ) m γ where
  plausible_step := PlausibleStep
  step_small := inferInstance
  step it := do
    haveI := it.inner.small
    match (← it.inner.inner.stepH).inflate with
    | .yield it' out h =>
      pure <| .deflate <| .yield (toIter ⟨it.inner.small, it.inner.b, it'⟩ m γ) out (.yield h)
    | .skip it' h =>
      pure <| .deflate <| .skip (toIter ⟨it.inner.small, it.inner.b, it'⟩ m γ) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)

def SigmaIterator.rel [∀ b, Iterator (α b) m γ] [∀ b, Finite (α b) m] :
    Iter (α := SigmaIterator α m γ) m γ → Iter (α := SigmaIterator α m γ) m γ → Prop :=
  InvImage
    (PSigma.Lex emptyRelation
      (β := fun b : β => Iter (α := α b) m γ)
      (fun _ => InvImage Iter.TerminationMeasures.Finite.rel Iter.finitelyManySteps))
    (fun it => ⟨it.inner.b.inflate (small := _), it.inner.inner⟩)

instance SigmaIterator.finitenessRelation {β : Type v} {α : β → Type w}
    [Monad m] [∀ b, Iterator (α b) m γ] [∀ b, Finite (α b) m] : FinitenessRelation (SigmaIterator α m γ) m where
  rel := SigmaIterator.rel
  wf := by
    apply InvImage.wf
    refine ⟨fun ⟨b, it⟩ => ?_⟩
    apply PSigma.lexAccessible
    · exact emptyWf.wf.apply b
    · intro
      apply InvImage.wf
      exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case yield =>
      cases h
      apply PSigma.Lex.right
      exact Iter.TerminationMeasures.Finite.rel_of_yield ‹_›
    case skip =>
      cases h
      apply PSigma.Lex.right
      exact Iter.TerminationMeasures.Finite.rel_of_skip ‹_›
    case done =>
      cases h

instance SigmaIterator.instIteratorToArray [Monad m] [∀ b, Iterator (α b) m γ] [∀ b, Finite (α b) m] :
    IteratorToArray (SigmaIterator α m γ) m :=
  .defaultImplementation

instance SigmaIterator.instIteratorFor [Monad m] [Monad n] [MonadLiftT m n] [∀ b, Iterator (α b) m γ] :
    IteratorFor (SigmaIterator α m γ) m n :=
  .defaultImplementation

end Dependent

section Iter

set_option pp.universes true in
@[always_inline, inline]
def Iter.flatMapD {α : Type w} {β : Type v} {α₂ : β → Type w}
    {γ : Type x} {m : Type w → Type w'}
    [Monad m] [Iterator α m β] [(b : β) → Iterator (α₂ b) m γ]
    (f : (b : β) → Iter (α := α₂ b) m γ)
    (it : Iter (α := α) m β) :=
  let motive : Subtype (∃ it : Iter (α := α) m β, it.plausible_output ·) → Type w :=
    fun b => α₂ b.val
  letI α_sigma := SigmaIterator motive m γ
  letI g (it : Iter (α := α) m β) (out : β) (h : it.plausible_output out) : Iter (α := α_sigma) m γ :=
    toIter (SigmaIterator.mk inferInstance (.deflate (Subtype.mk out (Exists.intro it h)) (small := _))
      (f (USquash.deflate (Subtype.mk out (Exists.intro it h))).inflate.val)) m γ
  (toIter (FlatMap.mk it none) m γ : Iter (α := FlatMap α g) m γ)

end Iter

end FlatMap
