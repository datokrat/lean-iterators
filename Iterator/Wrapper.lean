/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic

structure Iter (m β) [Iterator α m β] where
  inner : α

@[inline]
def toIter (m) (it : α) [Iterator α m β] : Iter (α := α) m β :=
  ⟨it⟩

instance {m} [Functor m] [Iterator α m β] : Iterator (Iter (α := α) m β) m β where
  yielded it it' b := Iterator.yielded m it.inner it'.inner b
  skipped it it' := Iterator.skipped m it.inner it'.inner
  finished it := Iterator.finished m it.inner
  step it := (match · with
    | .yield it' x h => .yield ⟨it'⟩ x h
    | .skip it' h => .skip ⟨it'⟩ h
    | .done h => .done h) <$> (Iterator.step it.inner)

instance [Functor m] [Iterator α m β] [Finite α m] : Finite (Iter (α := α) m β) m where
  wf := InvImage.wf (finiteIteratorWF ∘ Iter.inner ∘ FiniteIteratorWF.inner) Finite.wf

instance [Functor m] [Iterator α m β] [Productive α m] : Productive (Iter (α := α) m β) m where
  wf := InvImage.wf (productiveIteratorWF ∘ Iter.inner ∘ ProductiveIteratorWF.inner) Productive.wf

@[inline]
def Iter.step {α β : Type u} (m : Type u → Type w) [Functor m] [Iterator α m β] (it : Iter (α := α) m β) :
    m (IterStep.for m it) :=
  let step := Iterator.step (m := m) it
  step.f <$> step.el

@[inline]
def Iter.stepH [Functor m] [Iterator α m β] (it : Iter (α := α) m β) :=
  Iterator.step (m := m) it
