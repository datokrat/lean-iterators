/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic
import Iterator.Consumers.Collect
import Iterator.Consumers.Loop

/-!
This file provides the iterator combinator `IterM.drop`.
-/

variable {α : Type w} {m : Type w → Type w'} {β : Type v}

structure Drop (α : Type w) (m : Type w → Type w') (β : Type v) where
  remaining : Nat
  inner : IterM (α := α) m β

/--
Given an iterator `it` and a natural number `n`, `it.drop n` is an iterator that forwards all of
`it`'s output values except for the first `n`.

**Marble diagram:**

```text
it          ---a----b---c--d-e--⊥
it.drop 3   ---------------d-e--⊥

it          ---a--⊥
it.drop 3   ------⊥
```

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

_TODO_: prove `Productive`

**Performance:**

Currently, this combinator incurs an additional O(1) cost with each output of `it`, even when the iterator
does not drop any elements anymore.
-/
def IterM.drop (n : Nat) (it : IterM (α := α) m β) :=
  toIter (Drop.mk n it) m β

inductive Drop.PlausibleStep [Iterator α m β] (it : IterM (α := Drop α m β) m β) :
    (step : IterStep (IterM (α := Drop α m β) m β) β) → Prop where
  | drop : ∀ {it' out k}, it.inner.inner.plausible_step (.yield it' out) →
      it.inner.remaining = k + 1 → PlausibleStep it (.skip (it'.drop k))
  | skip : ∀ {it'}, it.inner.inner.plausible_step (.skip it') →
      PlausibleStep it (.skip (it'.drop it.inner.remaining))
  | done : it.inner.inner.plausible_step .done → PlausibleStep it .done
  | yield : ∀ {it' out}, it.inner.inner.plausible_step (.yield it' out) →
      it.inner.remaining = 0 → PlausibleStep it (.yield (it'.drop 0) out)

def Drop.step [Monad m] [Iterator α m β] (it : IterM (α := Drop α m β) m β) :
    HetT m (IterStep (IterM (α := Drop α m β) m β) β) := do
  match ← it.inner.inner.stepHet with
  | .yield it' out =>
    match it.inner.remaining with
    | 0 => return .yield (it'.drop 0) out
    | k + 1 => return .skip (it'.drop k)
  | .skip it' => return .skip (it'.drop it.inner.remaining)
  | .done => return .done

theorem Drop.PlausibleStep.char [Monad m] [Iterator α m β] {it : IterM (α := Drop α m β) m β} :
    Drop.PlausibleStep it = (Drop.step it).property := by
  ext step
  simp only [Drop.step, bind, HetT.bindH]
  constructor
  · intro h
    cases h
    all_goals
      refine ⟨_, ‹_›, ?_⟩
      simp_all [pure]
  · rintro ⟨step, hp, h⟩
    cases step
    case yield =>
      dsimp only at h
      split at h
      · cases h
        exact .yield hp ‹_›
      · cases h
        exact .drop hp ‹_›
    case skip =>
      cases h
      exact .skip hp
    case done =>
      cases h
      exact .done hp

instance [Monad m] [Iterator α m β] {it : IterM (α := Drop α m β) m β} :
    Small.{w} (Subtype <| Drop.PlausibleStep it) := by
  rw [Drop.PlausibleStep.char]
  exact (Drop.step it).small

instance Drop.instIterator [Monad m] [Iterator α m β] : Iterator (Drop α m β) m β where
  plausible_step := Drop.PlausibleStep
  step_small := inferInstance
  step it := do
    match (← it.inner.inner.stepH).inflate (small := _) with
    | .yield it' out h =>
      match h' : it.inner.remaining with
      | 0 => pure <| .deflate <| .yield (it'.drop 0) out (.yield h h')
      | k + 1 => pure <| .deflate <| .skip (it'.drop k) (.drop h h')
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.drop it.inner.remaining) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)

def Drop.rel (m : Type w → Type w') [Iterator α m β] [Finite α m] :
    IterM (α := Drop α m β) m β → IterM (α := Drop α m β) m β → Prop :=
  InvImage IterM.TerminationMeasures.Finite.rel (IterM.finitelyManySteps ∘ Drop.inner ∘ IterM.inner)

instance Drop.instFinitenessRelation [Iterator α m β] [Monad m] [Finite α m] :
    FinitenessRelation (Drop α m β) m where
  rel := Drop.rel m
  wf := by
    apply InvImage.wf
    exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case drop it' h' _ =>
      cases h
      apply IterM.TerminationMeasures.Finite.rel_of_yield
      exact h'
    case skip it' h' =>
      cases h
      apply IterM.TerminationMeasures.Finite.rel_of_skip
      exact h'
    case done h' =>
      cases h
    case yield it' out h' h'' =>
      cases h
      apply IterM.TerminationMeasures.Finite.rel_of_yield
      exact h'

instance Drop.instIteratorToArray [Monad m] [Iterator α m β] [Finite α m] : IteratorToArray (Drop α m β) m :=
  .defaultImplementation

instance Drop.instIteratorFor [Monad m] [Monad n] [MonadLiftT m n] [Iterator α m β] [Finite α m] :
    IteratorFor (Drop α m β) m n :=
  .defaultImplementation
