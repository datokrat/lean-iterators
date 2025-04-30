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

variable {α : Type u} {m : Type w → Type w'}

structure ListIterator (α : Type u) where
  list : List α

-- instance {α} : Iterator (ListIterator α) m α where
--   step it :=
--     (fun
--       | [] => .done
--       | x :: xs => .yield { list := xs } x) <$>
--     (pure it.list : IterationT m _)

-- /--
-- Returns a finite iterator for the given list.
-- The iterator yields the elements of the list in order and then terminates.
-- -/
-- @[always_inline, inline]
-- def List.iter {α : Type u} (l : List α) (m : Type u → Type w := by exact Id) [ComputableSmall.{w} α] :
--     Iter (α := ListIterator α) m α :=
--   toIter m { list := l }

-- instance : FinitenessRelation (ListIterator α) m where
--   rel := InvImage WellFoundedRelation.rel ListIterator.list
--   wf := InvImage.wf _ WellFoundedRelation.wf
--   subrelation {it it'} h := by
--     simp_wf
--     simp only [Iterator.step, IterationT.map_eq_mapH, IterationT.mapH, Pure.pure] at h
--     obtain ⟨step, h, _, rfl, rfl⟩ := h
--     cases it
--     split at h <;> simp_all [IterStep.successor]

instance {α : Type u} [Pure m] [UnivLE.{u, w}] : Iterator (ListIterator α) m α where
  state_small := inferInstance
  value_small := inferInstance
  plausible_step it
    | .yield it' out => it.list = out :: it'.list
    | .skip _ => False
    | .done => it.list = []
  step it := pure (match it with
        | ⟨[]⟩ => .deflate ⟨.done, rfl⟩
        | ⟨x :: xs⟩ => .deflate ⟨.yield ⟨xs⟩ x, rfl⟩)

/--
Returns a finite iterator for the given list.
The iterator yields the elements of the list in order and then terminates.
-/
@[always_inline, inline]
def List.iter {α : Type u} (l : List α) (m : Type u → Type w := by exact Id) [Pure m] :
    Iter (α := ListIterator α) m α :=
  toIter m { list := l }

instance [Pure m] [UnivLE.{u, w}] : FinitenessRelation (ListIterator α) m where
  rel := InvImage WellFoundedRelation.rel ListIterator.list
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step <;> simp_all [IterStep.successor, Iterator.plausible_step]

end ListIterator

section Unfold

universe u v

variable {α : Type u} {m : Type w → Type w'} {f : α → α}

structure UnfoldIterator (α : Type u) (f : α → α) where
  next : α

instance [Pure m] [UnivLE.{u, w}] : Iterator (UnfoldIterator α f) m α where
  state_small := inferInstance
  value_small := inferInstance
  plausible_step it
    | .yield it' out => out = it.next ∧ it' = ⟨f it.next⟩
    | .skip _ => False
    | .done => False
  step it := pure <| .deflate <| .yield ⟨f it.next⟩ it.next (by simp)

/--
Creates an infinite, productive iterator. First it yields `init`.
If the last step yielded `a`, the next will yield `f a`.
-/
@[inline]
def Iter.unfold (m : Type u → Type w') [Pure m] {α : Type u} (init : α) (f : α → α) :=
  toIter m <| UnfoldIterator.mk (f := f) init

instance [Pure m] [UnivLE.{u, w}] : ProductivenessRelation (UnfoldIterator α f) m where
  rel := emptyWf.rel
  wf := emptyWf.wf
  subrelation {it it'} h := by cases h

end Unfold
