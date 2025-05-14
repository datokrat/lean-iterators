/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic
import Iterator.Consumers.Collect
import Iterator.Consumers.Loop
import Iterator.Pure
import Init.Data.Nat.Lemmas

section ListIterator

variable {α : Type w} {m : Type w → Type w'}

structure ListIterator (α : Type w) where
  list : List α

/--
Returns a finite iterator for the given list.
The iterator yields the elements of the list in order and then terminates.
-/
@[always_inline, inline]
def List.iterM {α : Type w} (l : List α) (m : Type w → Type w') [Pure m] :
    IterM (α := ListIterator α) m α :=
  toIter { list := l } m α

@[always_inline, inline]
def List.iter {α : Type w} (l : List α) :
    Iter (α := ListIterator α) α :=
  ((l.iterM Id).toPureIter : Iter α)

instance {α : Type w} [Pure m] : Iterator (ListIterator α) m α where
  plausible_step it
    | .yield it' out => it.inner.list = out :: it'.inner.list
    | .skip _ => False
    | .done => it.inner.list = []
  step it := pure (match it with
        | ⟨⟨[]⟩⟩ => ⟨.done, rfl⟩
        | ⟨⟨x :: xs⟩⟩ => ⟨.yield (toIter ⟨xs⟩ m α) x, rfl⟩)

instance [Pure m] : FinitenessRelation (ListIterator α) m where
  rel := InvImage WellFoundedRelation.rel (ListIterator.list ∘ IterM.inner)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step <;> simp_all [IterStep.successor, IterM.plausible_step, Iterator.plausible_step]

instance {α : Type w} [Monad m] : IteratorToArray (ListIterator α) m :=
  .defaultImplementation

instance {α : Type w} [Monad m] : IteratorToArrayPartial (ListIterator α) m :=
  .defaultImplementation

instance {α : Type w} [Monad m] [Monad n] : IteratorFor (ListIterator α) m n :=
  .defaultImplementation

instance {α : Type w} [Monad m] [Monad n] : IteratorForPartial (ListIterator α) m n :=
  .defaultImplementation

end ListIterator

section Unfold

universe u v

variable {α : Type w} {m : Type w → Type w'} {f : α → α}

structure UnfoldIterator (α : Type u) (f : α → α) where
  next : α

instance [Pure m] : Iterator (UnfoldIterator α f) m α where
  plausible_step it
    | .yield it' out => out = it.inner.next ∧ it' = toIter ⟨f it.inner.next⟩ m α
    | .skip _ => False
    | .done => False
  step it := pure <| .yield (toIter ⟨f it.inner.next⟩ m α) it.inner.next (by simp)

/--
Creates an infinite, productive iterator. First it yields `init`.
If the last step yielded `a`, the next will yield `f a`.
-/
@[always_inline, inline]
def IterM.unfold (m : Type w → Type w') [Pure m] {α : Type w} (init : α) (f : α → α) :=
  toIter (UnfoldIterator.mk (f := f) init) m α

@[always_inline, inline]
def Iter.unfold {α : Type w} (init : α) (f : α → α) :=
  ((IterM.unfold Id init f).toPureIter : Iter α)

instance [Pure m] : ProductivenessRelation (UnfoldIterator α f) m where
  rel := emptyWf.rel
  wf := emptyWf.wf
  subrelation {it it'} h := by cases h

instance {α : Type w} {f : α → α} [Monad m] [Monad n] : IteratorFor (UnfoldIterator α f) m n :=
  .defaultImplementation

instance {α : Type w} {f : α → α} [Monad m] [Monad n] : IteratorForPartial (UnfoldIterator α f) m n :=
  .defaultImplementation

-- We do *not* implement `IteratorToArrayPartial` because there is no change at all that it will terminate.

end Unfold
