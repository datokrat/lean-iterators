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
This file provides the iterator combinator `Iter.drop`.
-/

variable {α : Type w} {m : Type w → Type w'} {β : Type v}

structure Drop (α : Type u) where
  remaining : Nat
  inner : α

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
def Iter.drop [Iterator α m β]
    (n : Nat) (it : Iter (α := α) m β) :=
  toIter (Drop.mk n it.inner) m β

def Drop.innerIter {α : Type w} {m : Type w → Type w'} {β : Type v}
    (it : Iter (α := Drop α) m β) : Iter (α := α) m β :=
  toIter it.inner.inner m β

inductive Drop.PlausibleStep [Iterator α m β] (it : Iter (α := Drop α) m β) :
    (step : IterStep (Iter (α := Drop α) m β) β) → Prop where
  | drop : ∀ {it' out k}, (innerIter it).plausible_step (.yield it' out) →
      it.inner.remaining = k + 1 → PlausibleStep it (.skip (it'.drop k))
  | skip : ∀ {it'}, (innerIter it).plausible_step (.skip it') →
      PlausibleStep it (.skip (it'.drop it.inner.remaining))
  | done : (innerIter it).plausible_step .done → PlausibleStep it .done
  | yield : ∀ {it' out}, (innerIter it).plausible_step (.yield it' out) →
      it.inner.remaining = 0 → PlausibleStep it (.yield (it'.drop 0) out)

instance [Iterator α m β] {it : Iter (α := Drop α) m β} :
    Small.{w} (Subtype <| Drop.PlausibleStep it) := sorry

instance Drop.instIterator [Monad m] [Iterator α m β] : Iterator (Drop α) m β where
  plausible_step := Drop.PlausibleStep
  step_small := inferInstance
  step it := do
    match (← (innerIter it).stepH).inflate (small := _) with
    | .yield it' out h =>
      match h' : it.inner.remaining with
      | 0 => pure <| .deflate <| .yield (it'.drop 0) out (.yield h h')
      | k + 1 => pure <| .deflate <| .skip (it'.drop k) (.drop h h')
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.drop it.inner.remaining) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)

def Drop.rel (m : Type w → Type w') [Iterator α m β] [Finite α m] :
    Iter (α := Drop α) m β → Iter (α := Drop α) m β → Prop :=
  InvImage Iter.TerminationMeasures.Finite.rel (Iter.finitelyManySteps ∘ Drop.innerIter)

instance Drop.instFinitenessRelation [Iterator α m β] [Monad m] [Finite α m] :
    FinitenessRelation (Drop α) m where
  rel := Drop.rel m
  wf := by
    apply InvImage.wf
    exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case drop it' h' _ =>
      cases h
      apply Iter.TerminationMeasures.Finite.rel_of_yield
      exact h'
    case skip it' h' =>
      cases h
      apply Iter.TerminationMeasures.Finite.rel_of_skip
      exact h'
    case done h' =>
      cases h
    case yield it' out h' h'' =>
      cases h
      apply Iter.TerminationMeasures.Finite.rel_of_yield
      exact h'

instance Drop.instIteratorToArray [Monad m] [Iterator α m β] [Finite α m] : IteratorToArray (Drop α) m :=
  .defaultImplementation

instance Drop.instIteratorFor [Monad m] [Monad n] [MonadLiftT m n] [Iterator α m β] :
    IteratorFor (Drop α) m n :=
  .defaultImplementation
