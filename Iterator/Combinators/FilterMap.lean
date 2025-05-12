/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic
import Iterator.Consumers.Collect
import Iterator.Consumers.Loop
import Iterator.HetT

/-!
This file provides iterator combinators for filtering and mapping.

* `IterM.filterMap` either modifies or drops each value based on an option-valued mapping function.
* `IterM.filter` drops some elements based on a predicate.
* `IterM.map` modifies each value based on a mapping function

Several variants of these combinators are provided:

* `M` suffix: monadic mapping function
* `H` suffix: heterogeneous variant that allows switching the monad and the universes.
-/

section FilterMapMH

universe u' v' u v

@[ext]
structure FilterMapMH (α : Type w) {β : Type v} {γ : Type v'}
    {m : Type w → Type w'} (f : β → HetT m (Option γ)) where
  inner : IterM (α := α) m β

variable {α : Type w} {m : Type w → Type w'} {β : Type v} {γ : Type v'}
    [Monad m] [Iterator α m β] {f : β → HetT m (Option γ)}

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
def IterM.filterMapMH [Monad m] [Iterator α m β] (f : β → HetT m (Option γ))
    (it : IterM (α := α) m β) : IterM (α := FilterMapMH α f) m γ :=
  toIter ⟨it⟩ m γ

def MapMH (α : Type w) {β : Type v} {γ : Type v'} {m : Type w → Type w'} [Functor m]
    (f : β → HetT m γ) :=
  FilterMapMH α (fun b => HetT.mapH some (f b))

inductive FilterMapMH.PlausibleStep (it : IterM (α := FilterMapMH α f) m γ) : (step : IterStep (IterM (α := FilterMapMH α f) m γ) γ) → Prop where
  | yieldNone : ∀ {it' out}, it.inner.inner.plausible_step (.yield it' out) →
      (f out).property none → PlausibleStep it (.skip (it'.filterMapMH f))
  | yieldSome : ∀ {it' out out'}, it.inner.inner.plausible_step (.yield it' out) →
      (f out).property (some out') → PlausibleStep it (.yield (it'.filterMapMH f) out')
  | skip : ∀ {it'}, it.inner.inner.plausible_step (.skip it') → PlausibleStep it (.skip (it'.filterMapMH f))
  | done : it.inner.inner.plausible_step .done → PlausibleStep it .done

def FilterMapMH.step (it : IterM (α := FilterMapMH α f) m γ) :
    HetT m (IterStep (IterM (α := FilterMapMH α f) m γ) γ) := do
  it.inner.inner.stepHet.bindH fun
  | .yield it' out => (f out).bindH fun
      | none => pure <| .skip (it'.filterMapMH f)
      | some out' => pure <| .yield (it'.filterMapMH f) out'
  | .skip it' => pure <| .skip (it'.filterMapMH f)
  | .done => pure <| .done

theorem FilterMapMH.PlausibleStep.char {it : IterM (α := FilterMapMH α f) m γ} :
    FilterMapMH.PlausibleStep it = (FilterMapMH.step it).property := by
  ext step
  simp only [FilterMapMH.step, HetT.bindH]
  constructor
  · intro h
    cases h
    case yieldNone it' out h h' =>
      exact ⟨_, h, _, h', rfl⟩
    case yieldSome it' out h h' =>
      exact ⟨_, h, _, h', rfl⟩
    case skip it' h =>
      exact ⟨_, h, rfl⟩
    case done h =>
      exact ⟨_, h, rfl⟩
  · rintro ⟨step, hp, h⟩
    cases step
    case yield it' out =>
      obtain ⟨out', h, h'⟩ := h
      match out' with
      | none =>
        cases h'
        exact .yieldNone hp h
      | some _ =>
        cases h'
        exact .yieldSome hp h
    case skip it' =>
      cases h
      exact .skip hp
    case done =>
      cases h
      exact .done hp

instance [Monad m] {it : IterM (α := FilterMapMH α f) m γ} :
    Small.{w} (Subtype <| FilterMapMH.PlausibleStep it) := by
  rw [FilterMapMH.PlausibleStep.char]
  exact (FilterMapMH.step it).small

instance FilterMapMH.instIterator : Iterator (FilterMapMH α f) m γ where
  plausible_step := FilterMapMH.PlausibleStep
  step_small := inferInstance
  step it := do
    let step ← it.inner.inner.stepH
    letI step' := step.inflate (small := _)
    match step' with
    | .yield it' out h => do
      match (← (f out).computation).inflate (small := _) with
      | ⟨none, h'⟩ => pure <| .deflate <| .skip (it'.filterMapMH f) (.yieldNone h h')
      | ⟨some out', h'⟩ => pure <| .deflate <| .yield (it'.filterMapMH f) out' (.yieldSome h h')
    | .skip it' h => pure <| .deflate <| .skip (it'.filterMapMH f) (.skip h)
    | .done h => pure <| .deflate <| .done (.done h)

instance {f : β → HetT m γ} :
    Iterator (MapMH α f) m γ :=
  inferInstanceAs <| Iterator (FilterMapMH α _) m γ

instance FilterMapMH.instFinitenessRelation [Finite α m] : FinitenessRelation (FilterMapMH α f) m where
  rel := InvImage IterM.plausible_successor_of (FilterMapMH.inner ∘ IterM.inner)
  wf := InvImage.wf _ Finite.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case yieldNone it' out h' h'' =>
      cases h
      exact IterM.plausible_successor_of_yield h'
    case yieldSome it' out h' h'' =>
      cases h
      exact IterM.plausible_successor_of_yield h'
    case skip it' h' =>
      cases h
      exact IterM.plausible_successor_of_skip h'
    case done h' =>
      cases h

instance {f : β → HetT m γ} [Finite α m] :
    Finite (MapMH α f) m :=
  inferInstanceAs <| Finite (FilterMapMH α _) m

instance {f : β → HetT m γ} [Productive α m] :
    ProductivenessRelation (MapMH α f) m where
  rel := InvImage IterM.plausible_skip_successor_of (FilterMapMH.inner ∘ IterM.inner)
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

instance FilterMapMH.instIteratorFor [Monad m] [Monad n] [MonadLiftT m n] [Iterator α m β] :
    IteratorFor (FilterMapMH α f) m n :=
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
      it.inner.inner

instance MapMH.instIteratorFor [Monad m] [Monad n] [MonadLiftT m n] [Iterator α m β] :
    IteratorFor (MapMH α f) m n :=
  .defaultImplementation

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
def IterM.mapMH [Monad m] [Iterator α m β] (f : β → HetT m γ) (it : IterM (α := α) m β) :
    IterM (α := MapMH α f) m γ :=
  toIter ⟨it⟩ m γ

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
def IterM.filterMH [Monad m] [Iterator α m β] (f : β → HetT m Bool) (it : IterM (α := α) m β) :=
  (it.filterMapMH (fun b => (f b).mapH (fun x => if x = true then some b else none)) : IterM m β)

end FilterMapMH

section FilterMapH

universe u' v' u v

variable {α : Type w} {β : Type v} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    {γ : Type v'} {f : β → Option γ} [Small.{w} γ]

@[inline]
def IterM.filterMapH (f : β → Option γ) (it : IterM (α := α) m β) :=
  (it.filterMapMH (fun b => pure (f b)) : IterM m γ)

@[inline]
def IterM.mapH (f : β → γ) (it : IterM (α := α) m β) :=
  (it.mapMH (fun b => pure (f b)) : IterM m γ)

end FilterMapH

section FilterMap

variable {m : Type w → Type w'} {α : Type w} {β : Type v} {γ : Type w} {f : β → Option γ}

@[inline]
def IterM.filterMap [Iterator α m β] [Monad m] (f : β → Option γ) (it : IterM (α := α) m β) :=
  (it.filterMapH f : IterM m γ)

@[inline]
def IterM.map [Iterator α m β] [Monad m] (f : β → γ) (it : IterM (α := α) m β) :=
  (it.mapH f : IterM m γ)

@[inline]
def IterM.filter [Iterator α m β] [Monad m] (f : β → Bool) (it : IterM (α := α) m β) :=
  (it.filterMapH (fun b => if f b then some b else none) : IterM m β)

end FilterMap

section FilterMapM

variable {m : Type w → Type w'} {α : Type w} {β : Type v} {γ : Type w} {f : β → Option γ}

@[inline]
def IterM.filterMapM [Iterator α m β] [Monad m] (f : β → m (Option γ)) (it : IterM (α := α) m β) :=
  (it.filterMapMH (fun b => monadLift (f b)) : IterM m γ)

@[inline]
def IterM.mapM [Iterator α m β] [Monad m] (f : β → m γ) (it : IterM (α := α) m β) :=
  (it.filterMapMH (fun b => some <$> monadLift (f b)) : IterM m γ)

@[inline]
def IterM.filterM [Iterator α m β] [Monad m] (f : β → m (USquash Bool)) (it : IterM (α := α) m β) :=
  (it.filterMapMH (fun b => (HetT.liftSquashed (f b)).mapH (if · = true then some b else none)) : IterM m β)

end FilterMapM
