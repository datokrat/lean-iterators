/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic
import Iterator.Consumers.Collect
import Iterator.Consumers.Loop

variable {α : Type w} {m : Type w → Type w'} {n : Type w → Type w''} {β : Type w}
    [Monad m] [Monad n]

structure MonadLiftIterator (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] (n : Type w → Type w'') [MonadLiftT m n] where
  inner : IterM (α := α) m β

inductive MonadLiftIterator.PlausibleStep {_ : Iterator α m β} {_ : MonadLiftT m n} (it : IterM (α := MonadLiftIterator α m n) n β) :
    IterStep (IterM (α := MonadLiftIterator α m n) n β) β → Prop where
  | yield {it' out} (h : it.inner.inner.plausible_step (.yield it' out)) :
      PlausibleStep it (.yield ⟨⟨it'⟩⟩ out)
  | skip {it'} (h : it.inner.inner.plausible_step (.skip it')) :
      PlausibleStep it (.skip ⟨⟨it'⟩⟩)
  | done (h : it.inner.inner.plausible_step .done) :
      PlausibleStep it .done

instance MonadLiftIterator.instIterator {_ : Iterator α m β} {_ : MonadLiftT m n} : Iterator (MonadLiftIterator α m n) n β where
  plausible_step := PlausibleStep
  step it := do
    match ← it.inner.inner.step with
    | .yield it' out h => pure <| .yield ⟨⟨it'⟩⟩ out (.yield h)
    | .skip it' h => pure <| .skip ⟨⟨it'⟩⟩ (.skip h)
    | .done h => pure <| .done (.done h)

instance {_ : Iterator α m β} [Finite α m] {_ : MonadLiftT m n} : FinitenessRelation (MonadLiftIterator α m n) n where
  rel := InvImage IterM.TerminationMeasures.Finite.rel fun it => it.inner.inner.finitelyManySteps
  wf := by
    apply InvImage.wf
    exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case yield it' out h =>
      cases h
      exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
    case skip it' h =>
      cases h
      exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
    case done h =>
      cases h

instance MonadLiftIterator.instIteratorFor [Monad n] [Monad n']
    [Iterator α m β] [Finite α m] {_ : MonadLiftT m n} :
    IteratorFor (MonadLiftIterator α m n) n n' :=
  .defaultImplementation

variable (n) in
@[always_inline, inline]
def IterM.monadLift [Iterator α m β] {_ : MonadLiftT m n} (it : IterM (α := α) m β) :=
  (toIter (MonadLiftIterator.mk it (m := m) (n := n)) n β : IterM n β)

@[always_inline, inline]
def IterM.switchMonad {α : Type w} {m : Type w → Type w'} {n : Type w → Type w''} {β : Type w}
    [Monad m] [Monad n] [Iterator α m β]
    (it : IterM (α := α) m β) (lift : ∀ {γ}, m γ → n γ) :=
  haveI : MonadLift m n := ⟨lift⟩
  (toIter (MonadLiftIterator.mk it (m := m) (n := n)) n β : IterM n β)
