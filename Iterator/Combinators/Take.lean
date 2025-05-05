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
This file provides the iterator combinator `Iter.take`.
-/

variable {α : Type w} {m : Type w → Type w'} {β : Type v}

structure Take (α : Type u) where
  remaining : Nat
  inner : α

def Take.innerIter {α : Type w} {m : Type w → Type w'} {β : Type v}
    (it : Iter (α := Take α) m β) : Iter (α := α) m β :=
  toIter it.inner.inner m β

def Take.mkOfInnerIter {α : Type w} {m : Type w → Type w'} {β : Type v}
    (it : Iter (α := α) m β) (remaining : Nat) : Iter (α := Take α) m β :=
  toIter ⟨remaining, it.inner⟩ m β

theorem Take.mkOfInnerIter_surjective {α : Type w} {m : Type w → Type w'} {β : Type v}
    (it : Iter (α := Take α) m β) :
    ∃ it₀ k, it = mkOfInnerIter it₀ k := by
  refine ⟨innerIter it, it.inner.remaining, rfl⟩

inductive Take.PlausibleStep [Iterator α m β] (it : Iter (α := Take α) m β) :
    (step : IterStep (Iter (α := Take α) m β) β) → Prop where
  | yield : ∀ {it' out k}, (innerIter it).plausible_step (.yield it' out) →
      it.inner.remaining = k + 1 → PlausibleStep it (.yield (mkOfInnerIter it' k) out)
  | skip : ∀ {it' k}, (innerIter it).plausible_step (.skip it') →
      it.inner.remaining = k + 1 → PlausibleStep it (.skip (mkOfInnerIter it' (k + 1)))
  | done : (innerIter it).plausible_step .done → PlausibleStep it .done
  | depleted : it.inner.remaining = 0 → PlausibleStep it .done

instance [Iterator α m β] {it : Iter (α := Take α) m β} :
    Small.{w} (Subtype <| Take.PlausibleStep it) := sorry

instance Take.instIterator [Monad m] [Iterator α m β] : Iterator (Take α) m β where
  plausible_step := Take.PlausibleStep
  step_small := inferInstance
  step it :=
    match h : it.inner.remaining with
    | 0 => pure <| .deflate <| .done (.depleted h)
    | k + 1 => do
      match (← (innerIter it).stepH).inflate (small := _) with
      | .yield it' out h' => pure <| .deflate <| .yield (mkOfInnerIter it' k) out (.yield h' h)
      | .skip it' h' => pure <| .deflate <| .skip (mkOfInnerIter it' (k + 1)) (.skip h' h)
      | .done h' => pure <| .deflate <| .done (.done h')

/--
Given an iterator `it` and a natural number `n`, `it.take n` is an iterator that outputs
up to the first `n` of `it`'s values in order and then terminates.

**Marble diagram:**

```text
it          ---a----b---c--d-e--⊥
it.take 3   ---a----b---c⊥

it          ---a--⊥
it.take 3   ---a--⊥
```

**Termination properties:**

* `Finite` instance: always ✓
* `Productive` instance: only if `it` is productive

_TODO_: prove `Productive`

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it`.
-/
@[inline]
def Iter.take [Monad m] [Iterator α m β]
    (n : Nat) (it : Iter (α := α) m β) :=
  toIter (Take.mk n it.inner) m β

def Take.rel (m : Type w → Type w') [Monad m] [Iterator α m β] [Productive α m] :
    Iter (α := Take α) m β → Iter (α := Take α) m β → Prop :=
  InvImage (Prod.Lex Nat.lt_wfRel.rel Iter.TerminationMeasures.Productive.rel)
    (fun it => (it.inner.remaining, (innerIter it).finitelyManySkips))

theorem Take.rel_of_remaining [Monad m] [Iterator α m β] [Productive α m] {it it' : Iter (α := Take α) m β}
    (h : it'.inner.remaining < it.inner.remaining) : Take.rel m it' it :=
  Prod.Lex.left _ _ h

theorem Take.rel_of_inner [Monad m] [Iterator α m β] [Productive α m] {remaining : Nat} {it it' : Iter (α := α) m β}
    (h : it'.finitelyManySkips.rel it.finitelyManySkips) :
    Take.rel m (mkOfInnerIter it' remaining) (mkOfInnerIter it remaining) :=
  Prod.Lex.right _ h

instance Take.instFinitenessRelation [Monad m] [Iterator α m β] [Productive α m] :
    FinitenessRelation (Take α) m where
  rel := Take.rel m
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact WellFoundedRelation.wf
    · apply InvImage.wf
      exact Productive.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case yield it' out k h' h'' =>
      cases h
      apply rel_of_remaining
      simp_all [mkOfInnerIter]
    case skip it' out k h' h'' =>
      cases h
      obtain ⟨it, k, rfl⟩ := mkOfInnerIter_surjective it
      cases h''
      apply Take.rel_of_inner
      exact h'
    case done _ =>
      cases h
    case depleted _ =>
      cases h

instance Take.instIteratorToArray [Monad m] [Iterator α m β] [Productive α m] : IteratorToArray (Take α) m :=
  .defaultImplementation

instance Take.instIteratorFor [Monad m] [Monad n] [MonadLiftT m n] [Iterator α m β] :
    IteratorFor (Take α) m n :=
  .defaultImplementation
  -- TODO: use [IteratorFor α m n]
    -- forIn {γ} it init successor_of stepper _ := by
    -- refine Prod.fst <$> (IteratorFor.forIn (α := α) (m := m) (n := n) (innerIter it) (γ := γ × Nat) (init, it.inner.remaining)
    --   (successor_of := fun b c c' => c.snd = c'.snd + 1) ?_ ?_)
    -- · exact fun b c => do
    --     let result ← stepper b c.fst
    --     return match result.val with
    --     | .yield x => .yield ⟨
    --     | .done x => sorry
    -- refine Subrelation.wf (r := InvImage Iter.TerminationMeasures.Finite.rel (fun p => (p.1).finitelyManySteps)) ?_ ?_
    -- · intro p' p h
    --   cases h
    --   · apply Iter.plausible_successor_of_skip
    --     rename_i h
    --     exact h.1
    --   · rename_i h
    --     obtain ⟨out, h, _⟩ := h -- Interesting: Moving `obtain` after `apply` leads to failure
    --     apply Iter.plausible_successor_of_yield
    --     exact h
