/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.SimpleIterator

variable {α : Type u} {m : Type w → Type w'} {n : Type w → Type w''} {β : Type v}
    [Monad m] [Monad n] [MonadLiftT m n] [Iterator α m β] [ComputableSmall.{w} α] [ComputableSmall.{w} β]

structure MonadLiftIterator (α : Type u) (m : Type w → Type w') (n : Type w → Type w'') where
  inner : α

instance [i : ComputableSmall.{w} α] : ComputableSmall.{w} (MonadLiftIterator α m n) :=
  i.equiv MonadLiftIterator.mk MonadLiftIterator.inner rfl rfl

instance : Iterator (MonadLiftIterator α m n) n β where
  plausible_step it step := Iterator.plausible_step m it.inner (step.map MonadLiftIterator.inner id)
  step it := do
    let liftedStep : CodensityT n (PlausibleIterStep.liftedFor m it.inner) := Iterator.step (m := m) it.inner |>.mapH PlausibleIterStep.up |>.run
    match ← liftedStep |>.mapH PlausibleIterStep.down with
    | .yield it' b h => pure <| .yield ⟨it'⟩ b h
    | .skip it' h => pure <| .skip ⟨it'⟩ h
    | .done h => pure <| .done h

instance [Finite α m] : Finite (MonadLiftIterator α m n) n where
  wf := by
    let r : FiniteIteratorWF α m → FiniteIteratorWF α m → Prop := FiniteIteratorWF.lt
    refine Subrelation.wf (r := ?_) ?_ ?_
    · exact InvImage (FiniteIteratorWF.lt (α := α) (m := m)) (finiteIteratorWF ∘ MonadLiftIterator.inner ∘ FiniteIteratorWF.inner)
    · intro x y h
      exact h
    · apply InvImage.wf
      exact Finite.wf

-- instance : SimpleIterator (MonadLiftIterator α m n) n β where
--   step it := do
--     let step ← (IterationT.step m it.inner).mapH IterStep.up |>.liftInnerMonad n |>.mapH IterStep.down
--     match step with
--     | .yield it' b _ => pure <| .yield ⟨it'⟩ b ⟨⟩
--     | .skip it' _ => pure <| .skip ⟨it'⟩ ⟨⟩
--     | .done _ => pure <| .done ⟨⟩

-- instance [Finite α m] : SimpleIterator.Finite (MonadLiftIterator α m n) n where
--   rel := InvImage FiniteIteratorWF.lt (finiteIteratorWF ∘ MonadLiftIterator.inner)
--   wf := InvImage.wf _ Finite.wf
--   subrelation {it it'} h := by
--     simp only [SimpleIterator.step, IterationT.mapH, Bind.bind] at h

variable (n) in
@[always_inline, inline]
def Iter.monadLift (it : Iter (α := α) m β) :=
  (toIter n (MonadLiftIterator.mk it.inner (m := m) (n := n)) : Iter n β)

@[always_inline, inline]
def Iter.switchMonad {α : Type u} {m : Type w → Type w'} {n : Type w → Type w''} {β : Type v}
    [Monad m] [Monad n] [Iterator α m β] [ComputableSmall.{w} α] [ComputableSmall.{w} β]
    (it : Iter (α := α) m β) (lift : ∀ {γ}, m γ → n γ) :=
  haveI : MonadLift m n := ⟨lift⟩
  (toIter n (MonadLiftIterator.mk it.inner (m := m) (n := n)) : Iter n β)
