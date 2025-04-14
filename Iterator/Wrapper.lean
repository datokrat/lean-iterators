/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic
import Iterator.Cont

structure Iter {α} (m β) [Iterator α m β] where
  inner : α

def Iter.Relations.yielded {α m β} [Iterator α m β] (it it' : Iter (α := α) m β) (output : β) : Prop :=
  Iterator.yielded m it.inner it'.inner output

def Iter.Relations.skipped {α m β} [Iterator α m β] (it it' : Iter (α := α) m β) : Prop :=
  Iterator.skipped m it.inner it'.inner

def Iter.Relations.done {α m β} [Iterator α m β] (it : Iter (α := α) m β) : Prop :=
  Iterator.finished m it.inner

inductive Iter.Step {α m β} [Iterator α m β] (it : Iter (α := α) m β) where
  | yield : (it' : Iter (α := α) m β) → (output : β) → Iter.Relations.yielded it it' output → it.Step
  | skip : (it' : Iter (α := α) m β) → Iter.Relations.skipped it it' → it.Step
  | done : Iter.Relations.done it → it.Step

@[always_inline, inline]
def Iter.Step.ofInternal {α m β} [Iterator α m β] {it : Iter (α := α) m β} : IterStep.for m it.inner → it.Step
  | .yield it' output h => .yield ⟨it'⟩ output h
  | .skip it' h => .skip ⟨it'⟩ h
  | .done h => .done h

@[inline]
def toIter (m) (it : α) [Iterator α m β] : Iter (α := α) m β :=
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

@[inline]
def Iter.step {α β : Type u} (m : Type u → Type w) [Monad m]
    [Iterator α m β] [SteppableIterator.{w} α m β] (it : Iter (α := α) m β) :
    m (Iter.Step it) :=
  Iter.Step.ofInternal <$> SteppableIterator.intoMonad m Bind.bind it.inner

@[inline]
def Iter.stepH {α : Type u} {m : Type w → Type w'} {β : Type v} [Monad m]
    [Iterator α m β] [SteppableIterator.{max u v w'} α m β] (it : Iter (α := α) m β) {γ} : ContT m γ (Iter.Step it) :=
  Iter.Step.ofInternal <$> SteppableIterator.intoMonad (ContT m γ) (fun x f h => x >>= (f · h)) it.inner

@[inline]
def Iter.terminationByFinite {α β m} [Iterator α m β] [Finite α m] (it : Iter (α := α) m β) : FiniteIteratorWF α m :=
  finiteIteratorWF it.inner
