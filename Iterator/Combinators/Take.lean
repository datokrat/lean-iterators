/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.AbstractIteration

/-!
This file provides the iterator combinator `Iter.take`.
-/

variable {α : Type u} {m : Type w → Type w'} {β : Type v}

structure Take (α : Type u) where
  remaining : Nat
  inner : α

set_option pp.universes true

instance [Monad m] [Iterator α m β] [SteppableIterator α m β] : SimpleIterator (Take α) m β where
  step it :=
    match it with
    | { remaining := 0, inner := _ } => pure <| .done ⟨⟩
    | { remaining := remaining' + 1, inner := it } =>
      matchStep (m := m) it
        (fun it' b => pure <| .yield ⟨remaining', it'⟩ b ⟨⟩)
        (fun it' => pure <| .skip ⟨remaining' + 1, it'⟩ ⟨⟩)
        (pure <| .done ⟨⟩)

instance [Monad m] [Iterator α m β] [SteppableIterator α m β] [SteppableIterator α m β] :
    SimpleIterator.CompatibleUniverses.{x, y} (Take α) m where
  compatible it := by
    simp [SimpleIterator.step]
    split
    · rfl
    · simp only [matchStep, matchStepH, IterationT.bindH]
      ext
      rw [iff_iff_eq]
      congr
      ext
      split <;> rfl

/--
Given an iterator `it` and a natural number `n`, `it.take n` is an iterator that outputs
up to the first `n` of `it`'s values in order and then terminates.

**Marble diagram:**

```text
it          ---a----b---c--d-e--⊥
it.take 3   ---a----b---c⊥

it          ---a--⊥
it.take 3   ---a--⊥
```

**Termination properties:**

* `Finite` instance: always ✓
* `Productive` instance: only if `it` is productive

_TODO_: prove `Productive`

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it`.
-/
@[inline]
def Iter.take [Iterator α m β] [SteppableIterator α m β] [Monad m] (n : Nat) (it : Iter (α := α) m β) :=
  toIter m <| Take.mk n it.inner

def Take.rel (m : Type w → Type w') [Iterator α m β] : Take α → Take α → Prop :=
  InvImage (Prod.Lex Nat.lt_wfRel.rel ProductiveIteratorWF.lt)
    (fun it => (it.remaining, productiveIteratorWF (m := m) it.inner))

theorem Take.rel_of_remaining [Iterator α m β] {it it' : Take α}
    (h : it'.remaining < it.remaining) : Take.rel m it' it :=
  Prod.Lex.left _ _ h

theorem Take.rel_of_inner [Iterator α m β] {remaining : Nat} {it it' : α}
    (h : (productiveIteratorWF (m := m) it').lt (productiveIteratorWF it)) :
    Take.rel m ⟨remaining, it'⟩ ⟨remaining, it⟩ :=
  Prod.Lex.right _ h

instance [Monad m] [Iterator α m β] [SteppableIterator α m β] [Productive α m] : SimpleIterator.Finite (Take α) m where
  rel := Take.rel m
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact WellFoundedRelation.wf
    · exact Productive.wf
  subrelation {it it'} h := by
    cases it
    simp only [SimpleIterator.step] at h
    split at h
    · cases successor_done.mp h
    · rename_i heq
      cases heq
      obtain ⟨_, _, hy, h⟩ | ⟨_, hs, h⟩ | ⟨hd, h⟩ := successor_matchStep h
      · cases successor_yield.mp h
        apply Take.rel_of_remaining
        simp
      · cases successor_skip.mp h
        apply Take.rel_of_inner
        exact hs
      · cases successor_done.mp h

#exit

variable {m} [Monad m] [Iterator α m β]

instance [Iterator α m β] [Monad m] : Iterator (Take α) m β :=
  Iteration.instIterator fun
    | { remaining := 0, inner := _ } => pure <| .done ⟨⟩
    | { remaining := remaining' + 1, inner := it } =>
      matchStep it
        (fun it' b => pure <| .yield ⟨remaining', it'⟩ b ⟨⟩)
        (fun it' => pure <| .skip ⟨remaining' + 1, it'⟩ ⟨⟩)
        (pure <| .done ⟨⟩)

/--
Given an iterator `it` and a natural number `n`, `it.take n` is an iterator that outputs
up to the first `n` of `it`'s values in order and then terminates.

**Marble diagram:**

```text
it          ---a----b---c--d-e--⊥
it.take 3   ---a----b---c⊥

it          ---a--⊥
it.take 3   ---a--⊥
```

**Termination properties:**

* `Finite` instance: always ✓
* `Productive` instance: only if `it` is productive

_TODO_: prove `Productive`

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it`.
-/
def Iter.take [Iterator α m β] [Monad m] (n : Nat) (it : Iter (α := α) m β) :=
  toIter m <| Take.mk n it.inner

def Take.rel (m : Type w → Type w') [Iterator α m β] : Take α → Take α → Prop :=
  InvImage (Prod.Lex Nat.lt_wfRel.rel ProductiveIteratorWF.lt)
    (fun it => (it.remaining, productiveIteratorWF (m := m) it.inner))

theorem Take.rel_of_remaining [Iterator α m β] {it it' : Take α}
    (h : it'.remaining < it.remaining) : Take.rel m it' it :=
  Prod.Lex.left _ _ h

theorem Take.rel_of_inner [Iterator α m β] {remaining : Nat} {it it' : α}
    (h : (productiveIteratorWF (m := m) it').lt (productiveIteratorWF it)) :
    Take.rel m ⟨remaining, it'⟩ ⟨remaining, it⟩ :=
  Prod.Lex.right _ h

instance [Iterator α m β] [Monad m] [Productive α m] : Finite (Take α) m := by
  refine finite_instIterator _ (rel := Take.rel m) ?_ ?_
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
