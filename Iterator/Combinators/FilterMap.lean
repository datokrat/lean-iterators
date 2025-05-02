/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Wrapper
import Iterator.Consumers.Collect

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
structure FilterMapMH (α : Type u) {β : Type v} {γ : Type v'} [Small.{w} γ]
    {m : Type w → Type w'} {p : Option γ → Prop} (f : β → m (USquash <| Subtype p)) where
  inner : α

def MapMH (α : Type u) {β : Type v} {γ : Type v'} {m : Type w → Type w'} [Functor m]
    [Small.{w} γ] {p : γ → Prop} (f : β → m (USquash <| Subtype p)) :=
  FilterMapMH α (γ := γ) (p := fun x => ∃ y, x = some y ∧ p y)
    (fun x => (USquash.deflate ∘ (fun y => ⟨some y.1, y.1, rfl, y.2⟩) ∘ USquash.inflate) <$> f x)

variable {α : Type u} {m : Type w → Type w'} {β : Type v} {γ : Type v'} [Small.{w} γ]
    [Monad m] [Iterator α m β] {p : Option γ → Prop} {f : β → m (USquash <| Subtype p)}

instance : Small.{w} (FilterMapMH α f) where
  h := haveI : Small.{w} α := Iterator.state_small m; ⟨{
    Target := USquash α
    deflate x := .deflate x.inner
    inflate x := .mk x.inflate
    deflate_inflate := by simp
    inflate_deflate := by simp
  }⟩

inductive FilterMapMH.PlausibleStep (it : FilterMapMH α f) : (step : IterStep (FilterMapMH α f) γ) → Prop where
  | yieldNone : ∀ {it' out}, Iterator.plausible_step m it.inner (.yield it'.inner out) → p none → PlausibleStep it (.skip it')
  | yieldSome : ∀ {it' out out'}, Iterator.plausible_step m it.inner (.yield it'.inner out) → p (some out') → PlausibleStep it (.yield it' out')
  | skip : ∀ {it'}, Iterator.plausible_step m it.inner (.skip it'.inner) → PlausibleStep it (.skip it')
  | done : Iterator.plausible_step m it.inner .done → PlausibleStep it .done

instance : Iterator (FilterMapMH α f) m γ where
  state_small := inferInstance
  value_small := inferInstance
  plausible_step := FilterMapMH.PlausibleStep
  step it := do
    let step ← Iterator.step (m := m) it.inner
    letI step' := step.inflate (small := _)
    match step' with
    | .yield it' out h => do
      match (← f out).inflate with
      | ⟨none, h'⟩ => pure <| .deflate <| .skip ⟨it'⟩ (.yieldNone h h')
      | ⟨some out', h'⟩ => pure <| .deflate <| .yield ⟨it'⟩ out' (.yieldSome h h')
    | .skip it' h => pure <| .deflate <| .skip ⟨it'⟩ (.skip h)
    | .done h => pure <| .deflate <| .done (.done h)

instance {p : γ → Prop} {f : β → m (USquash <| Subtype p)} :
    Iterator (MapMH α f) m γ :=
  inferInstanceAs <| Iterator (FilterMapMH α _) m γ

-- TODO: This proof needs to use internals of IterationT instead of relying on successor_yield
instance [Finite α m] : FinitenessRelation (FilterMapMH α f) m where
  rel := InvImage (Iterator.plausible_successor m) FilterMapMH.inner
  wf := InvImage.wf _ Finite.wf
  subrelation {it it'} h := by
    simp only [Iterator.plausible_successor, Iterator.plausible_step] at h
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case yieldNone it' out h' h'' =>
      cases h
      exact Iterator.successor_of_yield h'
    case yieldSome it' out h' h'' =>
      cases h
      exact Iterator.successor_of_yield h'
    case skip it' h' =>
      cases h
      exact Iterator.successor_of_skip h'
    case done h' =>
      cases h

instance {p : γ → Prop} {f : β → m (USquash <| Subtype p)} [Finite α m] :
    Finite (MapMH α f) m :=
  inferInstanceAs <| Finite (FilterMapMH α _) m

instance {p : γ → Prop} {f : β → m (USquash <| Subtype p)} [Productive α m] :
    ProductivenessRelation (MapMH α f) m where
  rel := InvImage (Iterator.plausible_skip m) FilterMapMH.inner
  wf := InvImage.wf _ Productive.wf
  subrelation {it it'} h := by
    simp only [Iterator.plausible_skip, Iterator.plausible_step] at h
    cases h
    case yieldNone it' out h h' =>
      simp at h
    case skip it' h =>
      exact h

instance {p : γ → Prop} {f : β → m (USquash <| Subtype p)} [Finite α m] :
    IteratorToArray (MapMH α f) m :=
  .defaultImplementation

/--
`map` operations allow for a more efficient implementation of `toArray`. For example,
`array.iter.map f |>.toArray happens in-place if possible.
-/
instance {p : γ → Prop} {f : β → m (USquash <| Subtype p)} [IteratorToArray α m] :
    IteratorToArray (MapMH α f) m where
  toArrayMapped g it :=
    IteratorToArray.toArrayMapped (fun x => do g (← f x).inflate) (toIter m it.inner.inner)

@[always_inline, inline]
def Iterator.filterMapMH [Monad m] [Iterator α m β] (f : β → m (USquash <| Subtype p)) (it : α) :
    FilterMapMH α (m := m) f :=
  ⟨it⟩

@[always_inline, inline]
def Iterator.mapMH [Monad m] [Iterator α m β] {p : γ → Prop} (f : β → m (USquash <| Subtype p)) (it : α) :
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
def Iter.filterMapMH [Monad m] {_ : Iterator α m β} (f : β → m (USquash <| Option γ))
    (it : Iter (α := α) m β) :=
  ((toIter m <| Iterator.filterMapMH (m := m) (p := fun _ => True)
    ((USquash.deflate ∘ (⟨·, True.intro⟩) ∘ USquash.inflate) <$> f ·) it.inner) : Iter m γ)

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
def Iter.mapMH [Monad m] {_ : Iterator α m β} (f : β → m (USquash γ)) (it : Iter (α := α) m β) :=
  (toIter m <| Iterator.mapMH (m := m) (p := fun _ => True)
    ((USquash.deflate ∘ (⟨·, True.intro⟩) ∘ USquash.inflate) <$> f ·) it.inner : Iter m γ)

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
def Iter.filterMH [Monad m] {_ : Iterator α m β} (f : β → m (USquash Bool)) (it : Iter (α := α) m β) :=
  haveI : Small.{w} β := Iterator.value_small α m
  it.filterMapMH
    (fun b => (USquash.deflate ∘ (if · = true then some b else none) ∘ USquash.inflate) <$> (f b))

end FilterMapMH

section FilterMapH

universe u' v' u v

variable {α : Type u} {β : Type v} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    {γ : Type v'} {f : β → Option γ} [Small.{w} γ]

@[inline]
def Iter.filterMapH (f : β → Option γ) (it : Iter (α := α) m β) :=
  (it.filterMapMH (pure ∘ USquash.deflate ∘ f) : Iter m γ)

@[inline]
def Iter.mapH (f : β → γ) (it : Iter (α := α) m β) :=
  (it.mapMH (pure ∘ USquash.deflate ∘ f) : Iter m γ)

end FilterMapH

section FilterMap

variable {m : Type w → Type w'} {α : Type u} {β : Type v} {γ : Type w} {f : β → Option γ}

@[inline]
def Iter.filterMap {_ : Iterator α m β} [Monad m] (f : β → Option γ) (it : Iter (α := α) m β) :=
  (it.filterMapH f : Iter m γ)

@[inline]
def Iter.map {_ : Iterator α m β} [Monad m] (f : β → γ) (it : Iter (α := α) m β) :=
  (it.mapH f : Iter m γ)

@[inline]
def Iter.filter {_ : Iterator α m β} [Monad m] (f : β → Bool) (it : Iter (α := α) m β) :=
  haveI : Small.{w} β := Iterator.value_small α m
  (it.filterMapH (fun b => if f b then some b else none) : Iter m β)

end FilterMap

section FilterMapM

variable {m : Type w → Type w'} {α : Type w} {β : Type v} {γ : Type w} {f : β → Option γ}

@[inline]
def Iter.filterMapM {_ : Iterator α m β} [Monad m] (f : β → m (Option γ)) (it : Iter (α := α) m β) :=
  (it.filterMapMH (USquash.deflate <$> f ·) : Iter m γ)

@[inline]
def Iter.mapM {_ : Iterator α m β} [Monad m] (f : β → m γ) (it : Iter (α := α) m β) :=
  (it.filterMapM (fun b => some <$> f b) : Iter m γ)

@[inline]
def Iter.filterM {_ : Iterator α m β} [Monad m] (f : β → m (USquash Bool)) (it : Iter (α := α) m β) :=
  haveI : Small.{w} β := Iterator.value_small α m
  (it.filterMapMH (fun b => (USquash.deflate ∘ (if · = true then some b else none) ∘ USquash.inflate) <$> f b) : Iter m β)

end FilterMapM
