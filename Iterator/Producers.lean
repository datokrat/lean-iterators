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
  step it :=
    (fun
      | [] => .done
      | x :: xs => .yield { list := xs } x) <$>
    (pure it.list : IterationT m _)

/--
Returns a finite iterator for the given list.
The iterator yields the elements of the list in order and then terminates.
-/
@[always_inline, inline]
def List.iter {α : Type u} (l : List α) (m : Type u → Type w := by exact Id) [ComputableSmall.{w} α] :
    Iter (α := ListIterator α) m α :=
  toIter m { list := l }

instance : FinitenessRelation (ListIterator α) m where
  rel := InvImage WellFoundedRelation.rel ListIterator.list
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    simp only [Iterator.step, IterationT.map_eq_mapH, IterationT.mapH, Pure.pure] at h
    obtain ⟨step, h, _, rfl, rfl⟩ := h
    cases it
    split at h <;> simp_all [IterStep.successor]

-- TODO
-- @[inline]
-- def List.iterH {α : Type u} (l : List α) (m) [Pure m] : Iter (α := ListIterator α) m α :=
--   toIter m { list := l }

end ListIterator

section Unfold

universe u v

variable {α : Type u} {m : Type w → Type w'} {f : α → α}

structure UnfoldIterator (α : Type u) (f : α → α) where
  next : α

instance : Iterator (UnfoldIterator α f) m α where
  step it := pure <| .yield ⟨f it.next⟩ it.next

/--
Creates an infinite, productive iterator. First it yields `init`.
If the last step yielded `a`, the next will yield `f a`.
-/
@[inline]
def Iter.unfold (m : Type w → Type w' := by exact Id) {α : Type u} (init : α) (f : α → α) [ComputableUnivLE.{u, w}] :=
  toIter m <| UnfoldIterator.mk (f := f) init

instance [Pure m] : ProductivenessRelation (UnfoldIterator α f) m where
  rel := emptyWf.rel
  wf := emptyWf.wf
  subrelation {it it'} h := by cases h

end Unfold
