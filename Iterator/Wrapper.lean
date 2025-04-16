/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic
import Iterator.Cont

structure Iter {α} (m β) [Iterator α m β] where
  inner : IterState α m

variable {α : Type w} {α' : Type u} {m : Type w → Type w'} {β : Type v}

def Iter.Relations.yielded [Iterator α m β] (it it' : Iter (α := α) m β) (output : β) : Prop :=
  Iterator.yielded (m := m) it.inner it'.inner (Iterator.βEquiv it.inner |>.hom output)

def Iter.Relations.skipped [Iterator α m β] (it it' : Iter (α := α) m β) : Prop :=
  Iterator.skipped it.inner it'.inner

def Iter.Relations.done [Iterator α m β] (it : Iter (α := α) m β) : Prop :=
  Iterator.done it.inner

structure Iter.EncodedStep [Iterator α m β] (it : Iter (α := α) m β) where
  inner : IterStep.for m it.inner

inductive Iter.Step [Iterator α m β] (it : Iter (α := α) m β) where
  | yield : (it' : Iter (α := α) m β) → (output : β) → Iter.Relations.yielded it it' output → it.Step
  | skip : (it' : Iter (α := α) m β) → Iter.Relations.skipped it it' → it.Step
  | done : Iter.Relations.done it → it.Step

@[always_inline, inline]
def Iter.EncodedStep.decode [Iterator α m β] {it : Iter (α := α) m β} (step : it.EncodedStep) : it.Step :=
  match step.inner with
  | .yield it' out h => .yield ⟨it'⟩ (Iterator.βEquiv it.inner |>.inv out) (by simp [Relations.yielded, Equiv.hom_inv, h])
  | .skip it' h => .skip ⟨it'⟩ h
  | .done h => .done h

@[always_inline, inline]
def Iter.EncodedStep.ofInternal [Iterator α m β] {it : Iter (α := α) m β} (step : IterStep.for m it.inner) : it.EncodedStep :=
  ⟨step⟩

@[always_inline, inline]
def toIter (m) [Iterator α m β] (it : IterState α m) : Iter (α := α) m β :=
  ⟨it⟩

-- instance {m} [Functor m] [Iterator α m β] : Iterator (Iter (α := α) m β) m β where
--   yielded it it' b := Iterator.yielded m it.inner it'.inner b
--   skipped it it' := Iterator.skipped m it.inner it'.inner
--   finished it := Iterator.finished m it.inner
--   step it := Iterator.step it.inner
--   decode it step := match Iterator.decode it.inner step with
--     | .yield it' x h => .yield ⟨it'⟩ x h
--     | .skip it' h => .skip ⟨it'⟩ h
--     | .done h => .done h

-- instance [Functor m] [Iterator α m β] [Finite α m] : Finite (Iter (α := α) m β) m where
--   wf := InvImage.wf (finiteIteratorWF ∘ Iter.inner ∘ FiniteIteratorWF.inner) Finite.wf

-- instance [Functor m] [Iterator α m β] [Productive α m] : Productive (Iter (α := α) m β) m where
--   wf := InvImage.wf (productiveIteratorWF ∘ Iter.inner ∘ ProductiveIteratorWF.inner) Productive.wf

@[always_inline, inline]
def Iter.stepH [Monad m]
    [Iterator α m β] (it : Iter (α := α) m β) : m it.EncodedStep :=
  Iter.EncodedStep.ofInternal <$> Iterator.step it.inner

@[always_inline, inline]
def Iter.stepCont [Monad m]
    [Iterator α m β] (it : Iter (α := α) m β) {γ} : ContT m γ it.Step :=
  fun h => it.stepH >>= (h ·.decode)

@[always_inline, inline]
def Iter.step {α β : Type w} (m : Type w → Type w) [Monad m]
    [Iterator α m β] (it : Iter (α := α) m β) : m (Iter.Step it) :=
  Iter.EncodedStep.decode <$> it.stepH

@[always_inline, inline]
def Iter.terminationByFinite [Iterator α m β] [Finite α m] (it : Iter (α := α) m β) : FiniteIteratorWF α m :=
  finiteIteratorWF it.inner
