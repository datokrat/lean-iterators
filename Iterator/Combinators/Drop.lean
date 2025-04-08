/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.AbstractIteration

structure Drop (α : Type u) where
  remaining : Nat
  inner : α

instance [Iterator α m β] [Monad m] : Iterator (Drop α) m β :=
  Iteration.instIterator fun it => do
    matchStep it.inner
      (fun it' b => match it.remaining with
        | 0 => pure <| .yield ⟨0, it'⟩ b ⟨⟩
        | remaining' + 1 => pure <| .skip ⟨remaining', it'⟩ ⟨⟩)
      (fun it' => pure <| .skip ⟨it.remaining, it'⟩ ⟨⟩)
      (pure <| .done ⟨⟩)

def Drop.rel [Iterator α m β] : Drop α → Drop α → Prop :=
  InvImage FiniteIteratorWF.lt (finiteIteratorWF ∘ Drop.inner)

instance [Iterator α m β] [Monad m] [Finite α] : Finite (Drop α) := by
  refine finite_instIterator _ (rel := Drop.rel) ?_ ?_
  · apply InvImage.wf
    exact Finite.wf
  · intro it it' h
    obtain ⟨_, _, hy, h⟩ | ⟨_, hs, h⟩ | ⟨hd, h⟩ := prop_successor_matchStep h
    · split at h
      · cases up_successor_yield.mp h
        exact Or.inl ⟨_, hy⟩
      · cases up_successor_skip.mp h
        exact Or.inl ⟨_, hy⟩
    · cases up_successor_skip.mp h
      exact Or.inr hs
    · cases up_successor_done.mp h
