/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Core
import Init.Classical
import Init.Ext
import Init.NotationExtra
import Init.TacticsExtra

/-!
# Iterators

This module provides an iterator framework.
An iterator is an abstraction of a sequence of values that may or may not terminate.
Collection types such as `List`, `Array` or `TreeMap` are supposed to provide iterators via
an `.iter` method.

Most users of the iterator API will just put together existing library functions that
create, combine and consumer iterators. Consider a simple example:

```lean
-- [1, 2, 3].iter : Iter Id Nat (with implicit argument α := ListIterator α)
#check [1, 2, 3].iter

#eval [1, 2, 3].iter.step

-- 12
#eval [1, 2, 3].iter.map (· * 2) |>.fold (init := 0) (· + ·)
```

Generally, an iterator is an element of an arbitrary type `α` that has an
`Iterator α m β` instance. Here, `m` is a monad and `β` is the type of out put values that
the iterator spits out. `Iter {α} m β` is just a wrapper around such `α` and it provides
many convenience functions that are available in field notation.

The heart of every iterator is its `step` function, which returns `m (IterStep α β ..)`.
Here, `IterStep` is an inductive type that either (1) provides an output value in `β` and a
successor iterator, (2) provides only a successor iterator with no output, or
(3) signals that the iterator has finished and will provide no more outputs.

The `step` function can also be used by hand:

```lean
def sumrec (l : List Nat) : Nat :=
  go (l.iter.map (2 * ·)) 0
where
  go it acc :=
    match it.step with
    | .yield it' n _ => go it' (acc + n)
    | .skip it' _ => go it' acc
    | .done _ => acc
  termination_by finiteIteratorWF it
```

In general, iterators do not need to terminate after finitely many steps. This example
works because the iterator type at hand has an instance of the `Finite` typeclass.
Iterators that may not terminate but will not end up in an infinite sequence of `.skip`
steps are called productive. This behavior is encoded in the `Productive` typeclass.

The framework is heavily inspired by Rust's iterator library and Haskell's streamly.
In particular, it is designed so that even complex iterators are compiled into efficient
loops (stream fusion).

## Module structure

### Basic iterator API

* This file, `Iterator.Basic`, contains the definition of `Iterator`, `Finite` and `Productive`.
* `Iterator.Wrapper` defines the convenience wrapper structure `Iter {α} m β`.
* Generators (i.e., `.iter` methods for various data types) are provided in `Iterator.Generators`.
* Combinators (i.e., ways to build new iterators out of existing ones) are provided in
  `Iterator.Combinators`.
* Consumers (i.e., ways to actually iterate over an iterator) are provided in `Iterator.Consumers`.

### Iterator implementation and verification API

This API is still experimental and should not be relied on. As soon as it is clear that no fundamental
changes are necessary, this disclaimer will be removed.

* `Iterator.AbstractIteration` provides a monad that simplifies the construction and verification
  (especially, verification of finiteness or productiveness) of iterators.
* `Iterator.IteratorMorphism` provides another means to prove an iterator to be finite or productive
  by means of defining a structure-preserving map into another iterator type that is known to be
  finite or productive.

### Examples and benchmarks

* `Iterator.Examples` showcases plausible use cases for the iterator library.
* `Iterator.Bench` contains some other use cases.
   They are used for performance measurements and the analysis of the generated IR.
* `Iterator.ProjectBatomorph` exemplifies a potential performance improvement by generating
  multiple loops instead of only one. This heavily relies on type-level programming and is thought
  to improve the performance of `Drop` and `Concat` (the latter of which we don't have yet).
* `Iterator.ProjectBigCrunch` is a proof of concept for an alternative iterator definitiion that has
  the advantage that the internal state of the iterator does not affect the universe level of the iterator
  itself. Instead, the iterator lives in the same universe as its outputs. The disadvantages: it requires some
  not totally obvious optimizations (such as erasing fuel variables and more) in order to achieve more
  than just asymptotically good performance, and it's quite difficult to iterate even a few steps over an
  iterator that has not been proven to be finite. It's also unclear how this can be generalized to the
  monadic setting.
-/

variable {α : Type u} {β : Type v}

inductive IterStep (α β) (yielded : α → β → Prop) (skipped : α → Prop) (finished : Prop) where
| yield : (it : α) → (b : β) → yielded it b → IterStep α β yielded skipped finished
| skip : (a : α) → skipped a → IterStep α β yielded skipped finished
| done : finished → IterStep α β yielded skipped finished

set_option pp.all true in
def IterStep.successor {yp sp fp} : IterStep α β yp sp fp → Option α
  | .yield it _ _ => some it
  | .skip it _ => some it
  | .done _ => none

class Iterator (α : Type u) (m : outParam (Type (max u v) → Type x)) (β : outParam (Type v)) where
  yielded : α → α → β → Prop
  skipped : α → α → Prop
  finished : α → Prop
  step : (a : α) → m (IterStep α β (yielded a) (skipped a) (finished a))

section Finite

structure FiniteIteratorWF (α : Type u) [Iterator α m β] where
  inner : α

def FiniteIteratorWF.lt {α m β} [Iterator α m β] (x y : FiniteIteratorWF α) : Prop :=
  (∃ b, Iterator.yielded y.inner x.inner b) ∨ Iterator.skipped y.inner x.inner

def finiteIteratorWF {α m β} [Iterator α m β] (it : α) : FiniteIteratorWF α :=
  ⟨it⟩

class Finite (α) [Iterator α m β] : Prop where
  wf : WellFounded (FiniteIteratorWF.lt (α := α))

instance [Iterator α m β] [Finite α] : WellFoundedRelation (FiniteIteratorWF α) where
  rel := FiniteIteratorWF.lt
  wf := Finite.wf

macro_rules | `(tactic| decreasing_trivial) => `(tactic| first | exact Or.inl ⟨_, ‹_›⟩ | exact Or.inr ‹_›)

end Finite

section Productive

structure ProductiveIteratorWF (α : Type u) [Iterator α m β] where
  inner : α

def ProductiveIteratorWF.lt {α m β} [Iterator α m β] (x y : ProductiveIteratorWF α) : Prop :=
  Iterator.skipped y.inner x.inner

def productiveIteratorWF {α m β} [Iterator α m β] (it : α) : ProductiveIteratorWF α :=
  ⟨it⟩

class Productive (α) [Iterator α m β] : Prop where
  wf : WellFounded (ProductiveIteratorWF.lt (α := α))

instance [Iterator α m β] [Productive α] : WellFoundedRelation (ProductiveIteratorWF α) where
  rel := ProductiveIteratorWF.lt
  wf := Productive.wf

theorem ProductiveIteratorWF.subrelation_finiteIteratorWF {α m β} [Iterator α m β] :
    Subrelation (α := ProductiveIteratorWF α)
      ProductiveIteratorWF.lt
      (InvImage FiniteIteratorWF.lt (finiteIteratorWF ∘ inner)) := by
  intro x y
  exact Or.inr

instance [Iterator α m β] [Finite α] : Productive α where
  wf := ProductiveIteratorWF.subrelation_finiteIteratorWF.wf (InvImage.wf _ Finite.wf)

end Productive
