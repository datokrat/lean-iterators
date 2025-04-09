/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.AbstractIteration

structure Take (α : Type u) where
  remaining : Nat
  inner : α

instance [Iterator α m β] [Monad m] : Iterator (Take α) m β :=
  Iteration.instIterator fun
    | { remaining := 0, inner := _ } => pure <| .done ⟨⟩
    | { remaining := remaining' + 1, inner := it } =>
      matchStep it
        (fun it' b => pure <| .yield ⟨remaining', it'⟩ b ⟨⟩)
        (fun it' => pure <| .skip ⟨remaining' + 1, it'⟩ ⟨⟩)
        (pure <| .done ⟨⟩)

def Iter.take [Iterator α m β] [Monad m] (n : Nat) (it : Iter (α := α) m β) :=
  toIter <| Take.mk n it.inner

def Take.rel [Iterator α m β] : Take α → Take α → Prop :=
  InvImage (Prod.Lex Nat.lt_wfRel.rel ProductiveIteratorWF.lt) (fun it => (it.remaining, productiveIteratorWF it.inner))

theorem Take.rel_of_remaining [Iterator α m β] {it it' : Take α}
    (h : it'.remaining < it.remaining) : Take.rel it' it :=
  Prod.Lex.left _ _ h

theorem Take.rel_of_inner [Iterator α m β] {remaining : Nat} {it it' : α}
    (h : (productiveIteratorWF it').lt (productiveIteratorWF it)) : Take.rel ⟨remaining, it'⟩ ⟨remaining, it⟩ :=
  Prod.Lex.right _ h

instance [Iterator α m β] [Monad m] [Productive α] : Finite (Take α) := by
  refine finite_instIterator _ (rel := Take.rel) ?_ ?_
  · apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact WellFoundedRelation.wf
    · exact Productive.wf
  · intro it it' h
    split at h
    · cases up_successor_done.mp h
    · obtain ⟨_, _, hy, h⟩ | ⟨_, hs, h⟩ | ⟨hd, h⟩ := prop_successor_matchStep h
      · cases up_successor_yield.mp h
        apply Take.rel_of_remaining
        simp
      · cases up_successor_skip.mp h
        apply Take.rel_of_inner
        exact hs
      · cases up_successor_done.mp h
