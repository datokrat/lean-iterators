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
import Iterator.IterationT
import Iterator.UnivLE

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

variable {α : Type u} {β : Type v}

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

class Iterator (α : Type u) (m : Type w → Type w') (β : outParam (Type v)) where
  step : α → IterationT m (IterStep α β)

-- abbrev PlausibleIterStep.for {α β} (m) [Iterator α m β] (it : α) :=
--   PlausibleIterStep (Iterator.plausible_step m it)

-- abbrev PlausibleIterStep.liftedFor {α β} (m) [Iterator α m β] (it : α) [ComputableSmall.{w} α] [ComputableSmall.{w} β] : Type w :=
--   PlausibleIterStep
--     (fun step => Iterator.plausible_step m it <| step.map ComputableSmall.down ComputableSmall.down)

-- @[always_inline, inline]
-- def PlausibleIterStep.up {α β m} [Iterator α m β] [ComputableSmall.{w} α] [ComputableSmall.{w} β]
--     {it : α} (step : PlausibleIterStep.for m it) : PlausibleIterStep.liftedFor m it :=
--   match step with
--   | .yield it' b h => .yield (ComputableSmall.up it') (ComputableSmall.up b) (by simp [IterStep.map, ComputableSmall.down_up, h])
--   | .skip it' h => .skip (ComputableSmall.up it') (by simp [IterStep.map, ComputableSmall.down_up, h])
--   | .done h => .done h

-- @[always_inline, inline]
-- def PlausibleIterStep.down {α β m} [Iterator α m β] {_ : ComputableSmall.{w} α} {_ : ComputableSmall.{w} β} {it : α}
--     (step : PlausibleIterStep.liftedFor m it) : PlausibleIterStep.for m it :=
--   match step with
--   | .yield it' b h => .yield (ComputableSmall.down it') (ComputableSmall.down b) h
--   | .skip it' h => .skip (ComputableSmall.down it') h
--   | .done h => .done h

section Finite

def Iterator.successor_of {α β} (m) [Iterator α m β] (x y : α) : Prop :=
  Iterator.step (m := m) y |>.mapH IterStep.successor |>.property (some x)
  -- (∃ b, Iterator.plausible_step m y.inner (.yield x.inner b)) ∨
  --   Iterator.plausible_step m y.inner (.skip x.inner)

class Finite (α m) [Iterator α m β] : Prop where
  wf : WellFounded (Iterator.successor_of (α := α) m)

theorem Iterator.successor_of_yield {α m β} [Iterator α m β] {x y : α} {out : β}
    (h : Iterator.step (m := m) y |>.property (.yield x out)) : Iterator.successor_of m x y :=
  ⟨_, rfl, h⟩

theorem Iterator.successor_of_skip {α m β} [Iterator α m β] {x y : α}
    (h : Iterator.step (m := m) y |>.property (.skip x)) : Iterator.successor_of m x y :=
  ⟨_, rfl, h⟩

end Finite

section Productive

def Iterator.skip_successor_of {α β} (m) [Iterator α m β] (x y : α) : Prop :=
  Iterator.step (m := m) y |>.property (.skip x)

class Productive (α m) [Iterator α m β] : Prop where
  wf : WellFounded (Iterator.skip_successor_of (α := α) m)

end Productive

variable (α m) in
class FinitenessRelation [Iterator α m β] where
  rel : α → α → Prop
  wf : WellFounded rel
  subrelation : {it it' : α} → ((Iterator.step (m := m) it).mapH IterStep.successor).property (some it') → rel it' it

variable (α m) in
class ProductivenessRelation [Iterator α m β] where
  rel : α → α → Prop
  wf : WellFounded rel
  subrelation : {it it' : α} → (Iterator.step (m := m) it).property (.skip it') → rel it' it

instance [Iterator α m β] [FinitenessRelation α m] : Finite α m where
  wf := by
    refine Subrelation.wf (r := FinitenessRelation.rel (m := m) β) ?_ ?_
    · intro x y h
      apply FinitenessRelation.subrelation
      exact h
    · apply InvImage.wf
      exact FinitenessRelation.wf

instance [Iterator α m β] [ProductivenessRelation α m] : Productive α m where
  wf := by
    refine Subrelation.wf (r := ProductivenessRelation.rel (m := m) β) ?_ ?_
    · intro x y h
      apply ProductivenessRelation.subrelation
      exact h
    · apply InvImage.wf
      exact ProductivenessRelation.wf

def matchStep {α β γ} (yield : α → β → γ) (skip : α → γ) (done : γ) (step : IterStep α β) : γ :=
  match step with
  | .yield it out => yield it out
  | .skip it => skip it
  | .done => done

-- def matchStepD {α β γ} (step : IterStep α β)
--     (yield : (it : α) → (out : β) → step = .yield it out → γ)
--     (skip : (it : α) → step = .skip it → γ) (done : step = .done → γ) : γ :=
--   match step with
--   | .yield it out => yield it out rfl
--   | .skip it => skip it rfl
--   | .done => done rfl

theorem apply_matchStep {α β γ δ} (f : γ → δ) {yield : α → β → γ} {skip : α → γ} {done : γ} {step : IterStep α β} :
    f (matchStep yield skip done step) = matchStep (yield · · |> f) (skip · |> f) (f done) step := by
  cases step <;> rfl

def matchStepComputation {m α β γ} (yield : α → β → IterationT m γ) (skip : α → IterationT m γ) (done : IterationT m γ) (step : IterStep α β) :
    CodensityT m (matchStep yield skip done step).Plausible :=
      match step with
      | .yield it out => (yield it out).computation
      | .skip it => (skip it).computation
      | .done => done.computation

def matchStepD {α β} {motive : IterStep α β → Type v}
    (yield : (it : α) → (out : β) → motive (.yield it out))
    (skip : (it : α) → motive (.skip it))
    (done : motive .done) (step : IterStep α β) :
    motive step :=
      match step with
      | .yield it out => (yield it out)
      | .skip it => (skip it)
      | .done => done

def matchStepComputation' {m α β γ} (yield : α → β → IterationT m γ) (skip : α → IterationT m γ) (done : IterationT m γ) (step : IterStep α β) :
    CodensityT m (matchStep yield skip done step).Plausible :=
      matchStepD (motive := fun step => CodensityT m (matchStep yield skip done step |>.Plausible))
        (yield · · |>.computation)
        (skip · |>.computation)
        done.computation
        step

theorem computation_matchStep {m α β γ} {yield : α → β → IterationT m γ} {skip : α → IterationT m γ} {done : IterationT m γ} {step : IterStep α β} :
    (matchStep yield skip done step).computation =
      matchStepD (motive := fun step => CodensityT m (matchStep yield skip done step |>.Plausible))
        (yield · · |>.computation)
        (skip · |>.computation)
        done.computation
        step := by
  cases step <;> rfl

theorem apply_matchStepD {α β} {motive : IterStep α β → Type v}
    {motive' : IterStep α β → Type v'}
    (yield : (it : α) → (out : β) → motive (.yield it out))
    (skip : (it : α) → motive (.skip it))
    (done : motive .done) (step : IterStep α β)
    {f : {step : IterStep α β} → motive step → motive' step} :
    f (matchStepD yield skip done step) =
      sorry := sorry

inductive MatchStepVerificationCases {α : Type u} {m : Type w → Type w'} {β : Type v} {γ : Type x}
    [Iterator α m β] (it : α) (yield : α → β → IterationT m γ) (skip : α → IterationT m γ)
    (done : IterationT m γ) (x : γ) : Prop where
  | yield {it' : α} {out : β} :
    (Iterator.step (m := m) it).property (.yield it' out) →
    (yield it' out).property x → MatchStepVerificationCases it yield skip done x
  | skip {it' : α} :
    (Iterator.step (m := m) it).property (.skip it') →
    (skip it').property x → MatchStepVerificationCases it yield skip done x
  | done :
    (Iterator.step (m := m) it).property .done →
    done.property x → MatchStepVerificationCases it yield skip done x

theorem successor_matchStepH {α : Type u} {m : Type w → Type w'} {β : Type v} {γ : Type x} {δ : Type y}
    [Iterator α m β]
    {it : α} {yield skip done}
    {f : γ → δ} {x : δ}
    (h : (IterationT.mapH f <| (Iterator.step (m := m) it).bindH <| matchStep (γ := IterationT m γ) yield skip done).property x) :
    MatchStepVerificationCases it (yield · · |>.mapH f) (skip · |>.mapH f) (done.mapH f) x := by
  simp only [IterationT.mapH, IterationT.bindH, matchStep] at h
  obtain ⟨c, rfl, _, h, h'⟩ := h
  split at h
  · exact .yield h' ⟨c, rfl, h⟩
  · exact .skip h' ⟨c, rfl, h⟩
  · exact .done h' ⟨c, rfl, h⟩

theorem successor_yield [Pure m] [Iterator α m β] {it₁ it₂ : α} {b : β} :
    ((pure (.yield it₁ b) : IterationT m (IterStep α β)).mapH IterStep.successor).property (some it₂) ↔
      it₂ = it₁ := by
  simp [IterationT.mapH, Pure.pure, IterStep.successor]

theorem successor_skip [Pure m] [Iterator α m β] {it₁ it₂ : α} :
    ((pure (.skip it₁) : IterationT m (IterStep α β)).mapH IterStep.successor).property (some it₂) ↔
      it₂ = it₁ := by
  simp [IterationT.mapH, Pure.pure, IterStep.successor]

theorem successor_done [Pure m] [Iterator α m β] {it: α} :
    ((pure .done : IterationT m (IterStep α β)).mapH IterStep.successor).property (some it) ↔ False := by
  simp [IterationT.mapH, Pure.pure, IterStep.successor]

theorem property_matchStepH {α : Type u} {m : Type w → Type w'} {β : Type v} {γ : Type x}
    [Iterator α m β] {it : α} {yield skip done} {x : γ}
    (h : (Iterator.step (m := m) it |>.bindH <| matchStep (γ := IterationT m γ) yield skip done).property x) :
    MatchStepVerificationCases it yield skip done x := by
  simp only [IterationT.bindH, matchStep] at h
  obtain ⟨c, h, h'⟩ := h
  split at h
  · exact .yield h' h
  · exact .skip h' h
  · exact .done h' h
