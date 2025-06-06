/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Core
import Init.Classical
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
-- [1, 2, 3].iter : IterM Id Nat (with implicit argument α := ListIterator α)
#check [1, 2, 3].iter

#eval [1, 2, 3].iter.step

-- 12
#eval [1, 2, 3].iter.map (· * 2) |>.fold (init := 0) (· + ·)
```

Generally, an iterator is an element of an arbitrary type `α` that has an
`Iterator α m β` instance. Here, `m` is a monad and `β` is the type of out put values that
the iterator spits out. `IterM {α} m β` is just a wrapper around such `α` and it provides
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
* `Iterator.Wrapper` defines the convenience wrapper structure `IterM {α} m β`.
* Producers (i.e., `.iter` methods for various data types) are provided in `Iterator.Producers`.
* Combinators (i.e., ways to build new iterators out of existing ones) are provided in
  `Iterator.Combinators`.
* Consumers (i.e., ways to actually iterate over an iterator) are provided in `Iterator.Consumers`.

### Iterator implementation and verification API

This API is still experimental and should not be relied on. As soon as it is clear that no fundamental
changes are necessary, this disclaimer will be removed.

* `Iterator.SimpleIterator` provides a convenient API for the implementation of iterator combinators.
  Building combinators by hand can be much more tedious.
* `Iterator.IteratorMorphism` provides another means to prove an iterator to be finite or productive
  by means of defining a structure-preserving map into another iterator type that is known to be
  finite or productive. (It's currently unused and broken.)

### Examples and benchmarks

* `Iterator.Examples` showcases plausible use cases for the iterator library.
* `Iterator.Bench` contains some other use cases.
   They are used for performance measurements and the analysis of the generated IR.
* `Iterator.ProjectBatomorph` exemplifies a potential performance improvement by generating
  multiple loops instead of only one. This heavily relies on type-level programming and is thought
  to improve the performance of `Drop` and `Concat` (the latter of which we don't have yet).
* `Iterator.ProjectBigCrunch` is a proof of concept for an alternative iterator definition that has
  the advantage that the internal state of the iterator does not affect the universe level of the iterator
  itself. Instead, the iterator lives in the same universe as its outputs. The disadvantages: it requires some
  not totally obvious optimizations (such as erasing fuel variables and more) in order to achieve more
  than just asymptotically good performance, and it's quite difficult to iterate even a few steps over an
  iterator that has not been proven to be finite. It's also unclear how this can be generalized to the
  monadic setting.
-/

structure IterM {α : Type w} (m : Type w → Type w') (β : Type v) : Type w where
  inner : α

section IterStep

variable {α : Type u} {β : Type w}

inductive IterStep (α β) where
| yield : (it : α) → (b : β) → IterStep α β
| skip : (a : α) → IterStep α β
| done : IterStep α β

def IterStep.successor : IterStep α β → Option α
  | .yield it _ => some it
  | .skip it => some it
  | .done => none

@[always_inline, inline]
def IterStep.map {α' : Type u'} {β' : Type v'} (f : α → α') (g : β → β') : IterStep α β → IterStep α' β'
  | .yield it out => .yield (f it) (g out)
  | .skip it => .skip (f it)
  | .done => .done

theorem IterStep.map_id {it : IterStep α β} :
    it.map id id = it := by
  simp only [map]
  cases it <;> simp

theorem IterStep.map_id' {it : IterStep α β} :
    it.map (·) (·) = it :=
  map_id

@[simp]
theorem IterStep.map_done {f : α → α'} {g : β → β'} :
  (.done : IterStep α β).map f g = .done := rfl

@[simp]
theorem IterStep.map_skip {f : α → α'} {g : β → β'} :
  (.skip it : IterStep α β).map f g = .skip (f it) := rfl

@[simp]
theorem IterStep.map_yield {f : α → α'} {g : β → β'} :
  (.yield it out : IterStep α β).map f g = .yield (f it) (g out) := rfl

theorem IterStep.map_map {α' : Type u'} {β' : Type v'} {f : α → α'} {g : β → β'}
    {α'' : Type u''} {β'' : Type v''} {f' : α' → α''} {g' : β' → β''} {it : IterStep α β} :
    (it.map f g).map f' g' = it.map (f · |> f') (g · |> g') := by
  simp only [map]
  cases it <;> simp

theorem IterStep.successor_map {α' : Type u'} {β' : Type v'} {f : α → α'} {g : β → β'} {step : IterStep α β} :
    (step.map f g).successor = step.successor.elim none (some <| f ·) := by
  cases step <;> rfl

def PlausibleIterStep (plausible_step : IterStep α β → Prop) := Subtype plausible_step

@[match_pattern]
def PlausibleIterStep.yield {plausible_step : IterStep α β → Prop}
    (it' : α) (out : β) (h : plausible_step (.yield it' out)) : PlausibleIterStep plausible_step :=
  ⟨.yield it' out, h⟩

@[match_pattern]
def PlausibleIterStep.skip {plausible_step : IterStep α β → Prop}
    (it' : α) (h : plausible_step (.skip it')) : PlausibleIterStep plausible_step :=
  ⟨.skip it', h⟩

@[match_pattern]
def PlausibleIterStep.done {plausible_step : IterStep α β → Prop}
    (h : plausible_step .done) : PlausibleIterStep plausible_step :=
  ⟨.done, h⟩

def PlausibleIterStep.successor (plausible_step : IterStep α β → Prop)
    (step : PlausibleIterStep plausible_step) : Option α :=
  step.val.successor

@[always_inline, inline]
def PlausibleIterStep.map {plausible_step : IterStep α β → Prop}
    {α' : Type u'} {β' : Type v'} (f : α → α') (g : β → β') (new_plausible_step : IterStep α' β' → Prop)
    (h : ∀ step : IterStep α β, plausible_step step → new_plausible_step (step.map f g))
    (step : PlausibleIterStep plausible_step) : PlausibleIterStep new_plausible_step :=
  ⟨step.val.map f g, h _ step.property⟩

theorem PlausibleIterStep.map_id {plausible_step : IterStep α β → Prop}
    {it : PlausibleIterStep plausible_step} :
    it.map id id plausible_step (by simp [IterStep.map_id]) = it := by
  simp only [map, IterStep.map]
  cases it <;> dsimp only <;> split <;> simp

end IterStep

-- theorem PlausiblerIterStep.map_map {α' : Type u'} {β' : Type v'} {f : α → α'} {g : β → β'}
--     {plausible_step : IterStep α β → Prop}
--     {plausible_step' : IterStep α' β' → Prop}
--     {plausible_step'' : IterStep α'' β'' → Prop} {h h'}
--     {α'' : Type u''} {β'' : Type v''} {f' : α' → α''} {g' : β' → β''} {it : PlausibleIterStep plausible_step} :
--     (it.map f g plausible_step' h).map f' g' plausible_step'' h' =
--       sorry := --it.map (f · |> f') (g · |> g') plausible_step'' sorry := by
--   sorry
--   -- simp only [map]
--   -- cases it <;> simp

class Iterator (α : Type w) (m : Type w → Type w') (β : outParam (Type w)) where
  plausible_step : IterM (α := α) m β → IterStep (IterM (α := α) m β) β → Prop
  step : (it : IterM (α := α) m β) → m (PlausibleIterStep <| plausible_step it)

@[always_inline, inline]
def toIter {α : Type w} (it : α) (m : Type w → Type w') (β : Type v) :
    IterM (α := α) m β :=
  ⟨it⟩

@[simp]
theorem toIter_inner {α m β} (it : IterM (α := α) m β) :
    toIter it.inner m β = it :=
  rfl

@[simp]
theorem inner_toIter {α m β} (it : α) :
    (toIter it m β).inner = it :=
  rfl

abbrev IterM.plausible_step {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β] :
    IterM (α := α) m β → IterStep (IterM (α := α) m β) β → Prop :=
  Iterator.plausible_step (α := α) (m := m)

abbrev IterM.Step {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it : IterM (α := α) m β) :=
  PlausibleIterStep it.plausible_step

def IterM.plausible_output {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it : IterM (α := α) m β) (out : β) : Prop :=
  ∃ it', it.plausible_step (.yield it' out)

def IterM.plausible_successor_of {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it' it : IterM (α := α) m β) : Prop :=
  ∃ step, step.successor = some it' ∧ it.plausible_step step

def IterM.plausible_skip_successor_of {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it' it : IterM (α := α) m β) : Prop :=
  it.plausible_step (.skip it')

def IterM.step {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it : IterM (α := α) m β) : m it.Step :=
  Iterator.step it

section Finite

class Finite (α m) [Iterator α m β] : Prop where
  wf : WellFounded (IterM.plausible_successor_of (α := α) (m := m))

structure IterM.TerminationMeasures.Finite
    (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] where
  it : IterM (α := α) m β

def IterM.TerminationMeasures.Finite.rel
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β] :
    TerminationMeasures.Finite α m → TerminationMeasures.Finite α m → Prop :=
  Relation.TransGen <| InvImage IterM.plausible_successor_of IterM.TerminationMeasures.Finite.it

instance {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [Finite α m] : WellFoundedRelation (IterM.TerminationMeasures.Finite α m) where
  rel := IterM.TerminationMeasures.Finite.rel
  wf := (InvImage.wf _ Finite.wf).transGen

def IterM.finitelyManySteps {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [Finite α m] (it : IterM (α := α) m β) : IterM.TerminationMeasures.Finite α m :=
  ⟨it⟩

theorem IterM.TerminationMeasures.Finite.rel_of_yield
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {it it' : IterM (α := α) m β} {out : β} (h : it.plausible_step (.yield it' out)) :
    rel ⟨it'⟩ ⟨it⟩ := by
  exact .single ⟨_, rfl, h⟩

theorem IterM.TerminationMeasures.Finite.rel_of_skip
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {it it' : IterM (α := α) m β} (h : it.plausible_step (.skip it')) :
    rel ⟨it'⟩ ⟨it⟩ := by
  exact .single ⟨_, rfl, h⟩

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
  | exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
  | exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›)

variable (α m) in
class FinitenessRelation [Iterator α m β] where
  rel : (IterM (α := α) m β) → (IterM (α := α) m β) → Prop
  wf : WellFounded rel
  subrelation : ∀ {it it'}, it'.plausible_successor_of it → rel it' it

instance [Iterator α m β] [FinitenessRelation α m] : Finite α m where
  wf := by
    refine Subrelation.wf (r := FinitenessRelation.rel) ?_ ?_
    · intro x y h
      apply FinitenessRelation.subrelation
      exact h
    · apply InvImage.wf
      exact FinitenessRelation.wf

theorem IterM.plausible_successor_of_yield
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {it' it : IterM (α := α) m β} {out : β} (h : it.plausible_step (.yield it' out)) :
    it'.plausible_successor_of it :=
  ⟨_, rfl, h⟩

theorem IterM.plausible_successor_of_skip
    {α m β} [Iterator α m β] {it it' : IterM (α := α) m β}
    (h : it.plausible_step (.skip it')) :
    it'.plausible_successor_of it :=
  ⟨_, rfl, h⟩

end Finite

section Productive

class Productive (α m) {β} [Iterator α m β] : Prop where
  wf : WellFounded (IterM.plausible_skip_successor_of (α := α) (m := m))

structure IterM.TerminationMeasures.Productive
    (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] where
  it : IterM (α := α) m β

def IterM.TerminationMeasures.Productive.rel
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β] :
    TerminationMeasures.Productive α m → TerminationMeasures.Productive α m → Prop :=
  Relation.TransGen <| InvImage IterM.plausible_skip_successor_of IterM.TerminationMeasures.Productive.it

instance {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [Productive α m] : WellFoundedRelation (IterM.TerminationMeasures.Productive α m) where
  rel := IterM.TerminationMeasures.Productive.rel
  wf := (InvImage.wf _ Productive.wf).transGen

def IterM.finitelyManySkips {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [Productive α m] (it : IterM (α := α) m β) : IterM.TerminationMeasures.Productive α m :=
  ⟨it⟩

theorem IterM.TerminationMeasures.Productive.rel_of_skip
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {it it' : IterM (α := α) m β} (h : it.plausible_step (.skip it')) :
    rel ⟨it'⟩ ⟨it⟩ :=
  .single h

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›)

variable (α m) in
class ProductivenessRelation [Iterator α m β] where
  rel : (IterM (α := α) m β) → (IterM (α := α) m β) → Prop
  wf : WellFounded rel
  subrelation : ∀ {it it'}, it'.plausible_skip_successor_of it → rel it' it

instance [Iterator α m β] [ProductivenessRelation α m] : Productive α m where
  wf := by
    refine Subrelation.wf (r := ProductivenessRelation.rel) ?_ ?_
    · intro x y h
      apply ProductivenessRelation.subrelation
      exact h
    · apply InvImage.wf
      exact ProductivenessRelation.wf

instance [Iterator α m β] [Finite α m] : Productive α m where
  wf := by
    apply Subrelation.wf (r := IterM.plausible_successor_of)
    · intro it' it h
      exact IterM.plausible_successor_of_skip h
    · exact Finite.wf

end Productive
