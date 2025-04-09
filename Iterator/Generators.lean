/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic
import Iterator.Combinators
import Init.Data.Nat.Lemmas

variable {m : Type u → Type u}

structure ListIterator (α : Type u) (m : Type u → Type u) where
  list : List α

instance [Pure m] : Iterator (ListIterator α m) m α where
  yielded it it' a := it.list = a :: it'.list
  skipped it it' := False
  finished it := it.list = []
  step
    | { list := .nil } => pure <| .done rfl
    | { list := x :: xs } => pure <| .yield { list := xs } x (by simp)

def List.iter {α} (l : List α) (m := Id) [Pure m] : Iter (α := ListIterator α m) m α :=
  toIter { list := l }

theorem test [Pure m] :
    Subrelation (FiniteIteratorWF.lt (α := ListIterator α m))
      (InvImage WellFoundedRelation.rel (ListIterator.list ∘ FiniteIteratorWF.inner)) := by
  intro x y hlt
  simp_wf
  simp only [FiniteIteratorWF.lt, Iterator.yielded, Iterator.skipped, or_false] at hlt
  cases hlt
  simp_all

instance [Pure m] : Finite (ListIterator α m) where
  wf := test.wf (InvImage.wf _ WellFoundedRelation.wf)
