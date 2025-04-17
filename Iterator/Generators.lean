/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic
import Iterator.Wrapper
import Init.Data.Nat.Lemmas

section ListIterator

variable {m : Type w → Type w'}

structure ListIterator (α : Type u) where
  list : List α

instance {α} : Iterator (ListIterator α) m α where
  yielded it it' a := it.list = a :: it'.list
  skipped _ _ := False
  done it := it.list = []
  step
    | { list := .nil } => pure <| .done rfl
    | { list := x :: xs } => pure <| .yield { list := xs } x rfl

-- TODO: check universes. It's _super_ weird that this works (note the w), but if I remove ComputableSmall,
-- it suddenly fails... It could produce the ComputableSmall.{u} instance either way
/--
Returns a finite iterator for the given list.
The iterator yields the elements of the list in order and then terminates.
-/
@[inline]
def List.iter {α : Type u} (l : List α) (m : Type u → Type w := by exact Id) [ComputableSmall.{w} α] :
    Iter (α := ListIterator α) m α :=
  toIter m { list := l }

-- TODO
-- @[inline]
-- def List.iterH {α : Type u} (l : List α) (m) [Pure m] : Iter (α := ListIterator α) m α :=
--   toIter m { list := l }

theorem ListIterator.subrelation :
    Subrelation (FiniteIteratorWF.lt (α := ListIterator α) (m := m))
      (InvImage WellFoundedRelation.rel (ListIterator.list ∘ FiniteIteratorWF.inner)) := by
  intro x y hlt
  simp_wf
  simp only [FiniteIteratorWF.lt, Iterator.yielded, Iterator.skipped, or_false] at hlt
  cases hlt
  simp_all

instance : Finite (ListIterator α) m where
  wf := ListIterator.subrelation.wf (InvImage.wf _ WellFoundedRelation.wf)

end ListIterator

section Unfold

universe u v

variable {α : Type u} {m : Type w → Type w'} {f : α → α}

structure UnfoldIterator (α : Type u) (f : α → α) where
  next : α

instance : Iterator (UnfoldIterator α f) m α where
  yielded it it' a := it.next = a ∧ it'.next = f a
  skipped _ _ := False
  done _ := False
  step
    | ⟨a⟩ => pure <| .yield ⟨f a⟩ a ⟨rfl, rfl⟩

/--
Creates an infinite, productive iterator. First it yields `init`.
If the last step yielded `a`, the next will yield `f a`.
-/
@[inline]
def Iter.unfold (m : Type w → Type w' := by exact Id) {α : Type u} (init : α) (f : α → α) [ComputableUnivLE.{u, w}] :=
  toIter m <| UnfoldIterator.mk (f := f) init

instance [Pure m] : Productive (UnfoldIterator α f) m where
  wf := by
    refine ⟨?_⟩
    intro x
    constructor
    rintro _ ⟨⟩

end Unfold
