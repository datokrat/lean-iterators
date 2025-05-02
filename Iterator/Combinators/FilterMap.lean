/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic
import Iterator.Consumers.Collect
import Iterator.HetT

/-!
This file provides iterator combinators for filtering and mapping.

* `Iter.filterMap` either modifies or drops each value based on an option-valued mapping function.
* `Iter.filter` drops some elements based on a predicate.
* `Iter.map` modifies each value based on a mapping function

Several variants of these combinators are provided:

* `M` suffix: monadic mapping function
* `H` suffix: heterogeneous variant that allows switching the monad and the universes.
-/

section FilterMapMH

universe u' v' u v

@[ext]
structure FilterMapMH (α : Type w) {β : Type v} {γ : Type v'}
    {m : Type w → Type w'} (f : β → HetT m (Option γ)) where
  inner : α

variable {α : Type w} {m : Type w → Type w'} {β : Type v} {γ : Type v'}
    [Monad m] [Iterator α m β] {f : β → HetT m (Option γ)}

def FilterMapMH.innerIter {α : Type w} {m : Type w → Type w'} {β : Type v}
    {γ : Type v'} {f : β → HetT m (Option γ)}
    (it : Iter (α := FilterMapMH α f) m γ) : Iter (α := α) m β :=
  toIter it.inner.inner m β

def FilterMapMH.mkOfInnerIter {α : Type w} {m : Type w → Type w'} {β : Type v}
    {γ : Type v'} {f : β → HetT m (Option γ)}
    (it : Iter (α := α) m β) : Iter (α := FilterMapMH α f) m γ :=
  toIter ⟨it.inner⟩ m γ

@[simp]
theorem FilterMapMH.innerIter_mkOfInnerIter {α : Type w} {m : Type w → Type w'} {β : Type v}
    {γ : Type v'} {f : β → HetT m (Option γ)}
    (it : Iter (α := α) m β) :
    innerIter (mkOfInnerIter it (f := f)) = it :=
  rfl

def MapMH (α : Type w) {β : Type v} {γ : Type v'} {m : Type w → Type w'} [Functor m]
    (f : β → HetT m γ) :=
  FilterMapMH α (fun b => HetT.mapH some (f b))

inductive FilterMapMH.PlausibleStep (it : Iter (α := FilterMapMH α f) m γ) : (step : IterStep (Iter (α := FilterMapMH α f) m γ) γ) → Prop where
  | yieldNone : ∀ {it' out}, (innerIter it).plausible_step (.yield it' out) →
      (f out).property none → PlausibleStep it (.skip (mkOfInnerIter it'))
  | yieldSome : ∀ {it' out out'}, (innerIter it).plausible_step (.yield it' out) →
      (f out).property (some out') → PlausibleStep it (.yield (mkOfInnerIter it') out')
  | skip : ∀ {it'}, (innerIter it).plausible_step (.skip it') → PlausibleStep it (.skip (mkOfInnerIter it'))
  | done : (innerIter it).plausible_step .done → PlausibleStep it .done

instance {it : Iter (α := FilterMapMH α f) m γ} :
    Small.{w} (Subtype <| FilterMapMH.PlausibleStep it) := sorry

instance FilterMapMH.instIterator : Iterator (FilterMapMH α f) m γ where
  plausible_step := FilterMapMH.PlausibleStep
  step_small := inferInstance
  step it := do
    let step ← (innerIter it).stepH
    letI step' := step.inflate (small := _)
    match step' with
    | .yield it' out h => do
      match (← (f out).computation).inflate (small := _) with
      | ⟨none, h'⟩ => pure <| .deflate <| .skip (mkOfInnerIter it') (.yieldNone h h')
      | ⟨some out', h'⟩ => pure <| .deflate <| .yield (mkOfInnerIter it') out' (.yieldSome h h')
    | .skip it' h => pure <| .deflate <| .skip (mkOfInnerIter it') (.skip h)
    | .done h => pure <| .deflate <| .done (.done h)

instance {f : β → HetT m γ} :
    Iterator (MapMH α f) m γ :=
  inferInstanceAs <| Iterator (FilterMapMH α _) m γ

instance FilterMapMH.instFinitenessRelation [Finite α m] : FinitenessRelation (FilterMapMH α f) m where
  rel := InvImage Iter.plausible_successor_of innerIter
  wf := InvImage.wf _ Finite.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case yieldNone it' out h' h'' =>
      cases h
      exact Iter.plausible_successor_of_yield h'
    case yieldSome it' out h' h'' =>
      cases h
      exact Iter.plausible_successor_of_yield h'
    case skip it' h' =>
      cases h
      exact Iter.plausible_successor_of_skip h'
    case done h' =>
      cases h

instance {f : β → HetT m γ} [Finite α m] :
    Finite (MapMH α f) m :=
  inferInstanceAs <| Finite (FilterMapMH α _) m

instance {f : β → HetT m γ} [Productive α m] :
    ProductivenessRelation (MapMH α f) m where
  rel := InvImage Iter.plausible_skip_successor_of FilterMapMH.innerIter
  wf := InvImage.wf _ Productive.wf
  subrelation {it it'} h := by
    cases h
    case yieldNone it' out h h' =>
      simp at h'
    case skip it' h =>
      exact h

instance {f : β → HetT m (Option γ)} [Finite α m] :
    IteratorToArray (FilterMapMH α f) m :=
  .defaultImplementation

/--
`map` operations allow for a more efficient implementation of `toArray`. For example,
`array.iter.map f |>.toArray happens in-place if possible.
-/
instance {f : β → HetT m γ} [IteratorToArray α m] :
    IteratorToArray (MapMH α f) m where
  toArrayMapped g it :=
    IteratorToArray.toArrayMapped
      (fun x => do g ((← (f x).computation).inflate (small := _)))
      (FilterMapMH.innerIter it)

@[always_inline, inline]
def Iterator.filterMapMH [Monad m] [Iterator α m β] (f : β → HetT m (Option γ)) (it : α) :
    FilterMapMH α (m := m) f :=
  ⟨it⟩

@[always_inline, inline]
def Iterator.mapMH [Monad m] [Iterator α m β] (f : β → HetT m γ) (it : α) :
    MapMH α (m := m) (f ·) :=
  ⟨it⟩

/--
Given an iterator `it`, a monadic `Option`-valued mapping function `f` and a monad transformation `mf`,
`it.filterMapMH f mf` is an iterator that applies `f` to each output of `it`. If `f` returns `none`,
the output is dropped. If it returns `some x`, then the iterator yields `x`.

**Marble diagram (without monadic effects):**

```text
it                 ---a --b--c --d-e--⊥
it.filterMapMH     ---a'-----c'-------⊥
```

(given that `f a = some a'`, `f c = some c'` and `f b = f d = d e = none`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: not available

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it` in addition to the cost of the monadic effects.
-/
@[inline]
def Iter.filterMapMH [Monad m] [Iterator α m β] (f : β → HetT m (Option γ))
    (it : Iter (α := α) m β) :=
  toIter (Iterator.filterMapMH f it.inner) m γ

/--
Given an iterator `it`, a monadic mapping function `f` and a monad transformation `mf`,
`it.mapMH f mf` is an iterator that applies `f` to each output of `it`. If `f` returns `none`,
the output is dropped. If it returns `some x`, then the iterator yields `x`.

**Marble diagram (without monadic effects):**

```text
it                 ---a --b --c --d -e --⊥
it.mapMH           ---a'--b'--c'--d'-e'--⊥
```

(given that `f a = a'` and so on)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

_TODO_: prove `Productive`. This requires us to wrap the FilterMapMH into a new type.

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it` in addition to the cost of the monadic effects.
-/
@[inline]
def Iter.mapMH [Monad m] [Iterator α m β] (f : β → HetT m γ) (it : Iter (α := α) m β) :=
  toIter (Iterator.mapMH f it.inner) m γ

/--
Given an iterator `it`, a monadic predicate `p` and a monad transformation `mf`,
`it.filterMH p mf` is an iterator that applies `p` to each output of `it`. If `p` returns `false`,
the output is dropped. Otherwise, the iterator forwards the output of `it`.

**Marble diagram (without monadic effects):**

```text
it                 ---a--b--c--d-e--⊥
it.filterMH        ---a-----c-------⊥
```

(given that `f a = f c = true'` and `f b = f d = d e = false`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: not available

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it` in addition to the cost of the monadic effects.
-/
@[inline]
def Iter.filterMH [Monad m] [Iterator α m β] (f : β → HetT m Bool) (it : Iter (α := α) m β) :=
  (it.filterMapMH (fun b => (f b).mapH (fun x => if x = true then some b else none)) : Iter m β)

end FilterMapMH

section FilterMapH

universe u' v' u v

variable {α : Type w} {β : Type v} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    {γ : Type v'} {f : β → Option γ} [Small.{w} γ]

@[inline]
def Iter.filterMapH (f : β → Option γ) (it : Iter (α := α) m β) :=
  (it.filterMapMH (fun b => pure (f b)) : Iter m γ)

@[inline]
def Iter.mapH (f : β → γ) (it : Iter (α := α) m β) :=
  (it.mapMH (fun b => pure (f b)) : Iter m γ)

end FilterMapH

section FilterMap

variable {m : Type w → Type w'} {α : Type w} {β : Type v} {γ : Type w} {f : β → Option γ}

@[inline]
def Iter.filterMap [Iterator α m β] [Monad m] (f : β → Option γ) (it : Iter (α := α) m β) :=
  (it.filterMapH f : Iter m γ)

@[inline]
def Iter.map [Iterator α m β] [Monad m] (f : β → γ) (it : Iter (α := α) m β) :=
  (it.mapH f : Iter m γ)

@[inline]
def Iter.filter [Iterator α m β] [Monad m] (f : β → Bool) (it : Iter (α := α) m β) :=
  (it.filterMapH (fun b => if f b then some b else none) : Iter m β)

end FilterMap

section FilterMapM

variable {m : Type w → Type w'} {α : Type w} {β : Type v} {γ : Type w} {f : β → Option γ}

@[inline]
def Iter.filterMapM [Iterator α m β] [Monad m] (f : β → m (Option γ)) (it : Iter (α := α) m β) :=
  (it.filterMapMH (fun b => monadLift (f b)) : Iter m γ)

@[inline]
def Iter.mapM [Iterator α m β] [Monad m] (f : β → m γ) (it : Iter (α := α) m β) :=
  (it.filterMapMH (fun b => some <$> monadLift (f b)) : Iter m γ)

@[inline]
def Iter.filterM [Iterator α m β] [Monad m] (f : β → m (USquash Bool)) (it : Iter (α := α) m β) :=
  (it.filterMapMH (fun b => (HetT.liftSquashed (f b)).mapH (if · = true then some b else none)) : Iter m β)

end FilterMapM
