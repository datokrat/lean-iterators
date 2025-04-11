/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.AbstractIteration

/-!
This file provides the iterator combinator `Iter.drop`.
-/

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

/--
Given an iterator `it` and a natural number `n`, `it.drop n` is an iterator that forwards all of
`it`'s output values except for the first `n`.

**Marble diagram:**

```text
it          ---a----b---c--d-e--⊥
it.drop 3   ---------------d-e--⊥

it          ---a--⊥
it.drop 3   ------⊥
```

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

_TODO_: prove `Productive`

**Performance:**

Currently, this combinator incurs an additional O(1) cost with each output of `it`, even when the iterator
does not drop any elements anymore.
-/
def Iter.drop [Iterator α m β] [Monad m] (n : Nat) (it : Iter (α := α) m β) :=
  toIter m <| Drop.mk n it.inner

def Drop.rel (m : Type w → Type w') [Iterator α m β] : Drop α → Drop α → Prop :=
  InvImage FiniteIteratorWF.lt (finiteIteratorWF (m := m) ∘ Drop.inner)

instance [Iterator α m β] [Monad m] [Finite α m] : Finite (Drop α) m := by
  refine finite_instIterator (m := m) _ (rel := Drop.rel m) ?_ ?_
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
