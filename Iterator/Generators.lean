/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic
import Iterator.Combinators
import Init.Data.Nat.Lemmas

section ListIterator

variable {m : Type u → Type v}

structure ListIterator (α : Type u) (m : Type u → Type v) where
  list : List α

instance [Pure m] : Iterator (ListIterator α m) m α where
  yielded it it' a := it.list = a :: it'.list
  skipped it it' := False
  finished it := it.list = []
  step
    | { list := .nil } => pure <| .done rfl
    | { list := x :: xs } => pure <| .yield { list := xs } x (by simp)

/--
Returns a finite iterator for the given list.
The iterator yields the elements of the list in order and then terminates.
-/
@[inline]
def List.iter {α} (l : List α) (m := Id) [Pure m] : Iter (α := ListIterator α m) m α :=
  toIter { list := l }

theorem ListIterator.subrelation [Pure m] :
    Subrelation (FiniteIteratorWF.lt (α := ListIterator α m))
      (InvImage WellFoundedRelation.rel (ListIterator.list ∘ FiniteIteratorWF.inner)) := by
  intro x y hlt
  simp_wf
  simp only [FiniteIteratorWF.lt, Iterator.yielded, Iterator.skipped, or_false] at hlt
  cases hlt
  simp_all

instance [Pure m] : Finite (ListIterator α m) where
  wf := ListIterator.subrelation.wf (InvImage.wf _ WellFoundedRelation.wf)

end ListIterator

section Unfold

universe u v

variable {m : Type u → Type v}

structure UnfoldIterator (α : Type u) (f : α → α) (m : Type u → Type v) where
  next : α

instance [Pure m] : Iterator (UnfoldIterator α f m) m α where
  yielded it it' a := it.next = a ∧ it'.next = f a
  skipped _ _ := False
  finished _ := False
  step | ⟨a⟩ => pure <| .yield ⟨f a⟩ a ⟨rfl, rfl⟩

/--
Creates an infinite, productive iterator. First it yields `init`.
If the last step yielded `a`, the next will yield `f a`.
-/
@[inline]
def Iter.unfold {α : Type u} (init : α) (f : α → α) (m : Type u → Type v := by exact Id) [Pure m] :=
  toIter <| UnfoldIterator.mk (f := f) (m := m) init

instance [Pure m] : Productive (UnfoldIterator α f m) where
  wf := by
    refine ⟨?_⟩
    intro x
    constructor
    rintro _ ⟨⟩

end Unfold
