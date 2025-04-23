/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.SimpleIterator

/-!
This file provides the iterator combinator `Iter.drop`.
-/

variable {α : Type u} {m : Type w → Type w'} {β : Type v}

structure Drop (α : Type u) where
  remaining : Nat
  inner : α

instance [Monad m] [Iterator α m β] : SimpleIterator (Drop α) m β where
  step it := matchStep (m := m) it.inner
      (fun it' b => match it.remaining with
        | 0 => pure <| .yield ⟨0, it'⟩ b
        | remaining' + 1 => pure <| .skip ⟨remaining', it'⟩)
      (fun it' => pure <| .skip ⟨it.remaining, it'⟩)
      (pure <| .done)

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
def Iter.drop [Iterator α m β] [Monad m] [ComputableUnivLE.{u, w}] {small : ComputableSmall.{w} α}
    (n : Nat) (it : Iter (α := α) m β (small := small)) :=
  toIter (α := Drop α) m <| Drop.mk n it.inner

def Drop.rel (m : Type w → Type w') [Iterator α m β] : Drop α → Drop α → Prop :=
  InvImage FiniteIteratorWF.lt (finiteIteratorWF (m := m) ∘ Drop.inner)

instance [Iterator α m β] [Monad m] [Finite α m] : SimpleIterator.Finite (Drop α) m where
  rel := Drop.rel m
  wf := by
    apply InvImage.wf
    exact Finite.wf
  subrelation {it it'} h := by
    simp only [SimpleIterator.step] at h
    obtain ⟨_, _, hy, h⟩ | ⟨_, hs, h⟩ | ⟨hd, h⟩ := successor_matchStep h
    · split at h
      · cases successor_yield.mp h
        exact Or.inl ⟨_, hy⟩
      · cases successor_skip.mp h
        exact Or.inl ⟨_, hy⟩
    · cases successor_skip.mp h
      exact Or.inr hs
    · cases successor_done.mp h
