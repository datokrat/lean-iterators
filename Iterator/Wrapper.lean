/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic
import Iterator.Cont

variable {α : Type u} {m : Type w → Type w'} {β : Type v}

structure Iter {α : Type u} (m : Type w → Type w') (β : Type v)
    [Iterator α m β] [ComputableSmall.{w} α] : Type w where
  innerLifted : ComputableSmall.Lift α

variable (m) in
@[always_inline, inline]
def toIter [Iterator α m β] [ComputableSmall.{w} α] (it : α) : Iter (α := α) m β :=
  ⟨ComputableSmall.up it⟩

@[always_inline, inline]
def Iter.inner {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (it : Iter (α := α) m β) : α :=
  ComputableSmall.down it.innerLifted

@[simp]
theorem inner_toIter {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (it : α) :
    (toIter m it).inner = it :=
  ComputableSmall.down_up

inductive Iter.Step {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (it : Iter (α := α) m β) where
| yield : (it' : Iter (α := α) m β) → (b : β) → Iterator.yielded m it.inner it'.inner b → it.Step
| skip : (it' : Iter (α := α) m β) → Iterator.skipped m it.inner it'.inner → it.Step
| done : Iterator.done m it.inner → it.Step

@[always_inline, inline]
def Iter.Step.ofInternal {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (it : Iter (α := α) m β) (step : IterStep.for m it.inner) :
    it.Step :=
  match step with
  | .yield it' b h => .yield (toIter m it') b (by simp only [inner_toIter, h])
  | .skip it' h => .skip (toIter m it') (by simp only [inner_toIter, h])
  | .done h => .done h

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
def Iter.stepH [Monad m] {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (it : Iter (α := α) m β) :
    CodensityT m it.Step :=
  Iterator.step it.inner |>.mapH (Iter.Step.ofInternal it)

@[always_inline, inline]
def Iter.step {β : Type w} [Monad m] {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (it : Iter (α := α) m β) :
    m (Iter.Step it) :=
  it.stepH.run

@[always_inline, inline]
def Iter.terminationByFinite {_ : Iterator α m β} {_ : ComputableSmall.{w} α} [Finite α m] (it : Iter (α := α) m β) :
    FiniteIteratorWF α m :=
  finiteIteratorWF it.inner
