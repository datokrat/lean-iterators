/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Wrapper
import Iterator.SimpleIterator

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
structure FilterMapMH (α : Type u) {β : Type v} {γ : Type v'}
    {m : Type w → Type w'} (f : β → IterationT m (Option γ)) where
  inner : α

def MapMH (α : Type u) {β : Type v} {γ : Type v'} {m : Type w → Type w'} (f : β → IterationT m γ) :=
  FilterMapMH α (some <$> f ·)

variable {α : Type u} {m : Type w → Type w'} {β : Type v} {γ : Type v'}
    [Monad m] [Iterator α m β]
    {f : β → IterationT m (Option γ)}

instance [i : ComputableSmall.{w} α] : ComputableSmall.{w} (FilterMapMH α f) :=
  i.equiv FilterMapMH.mk FilterMapMH.inner rfl rfl

instance [i : ComputableSmall.{w} α] {f : β → IterationT m γ} : ComputableSmall.{w} (MapMH α f) :=
  instComputableSmallFilterMapMH

instance : SimpleIterator (FilterMapMH α f) m γ where
  step it :=
    matchStepH (m := m) it.inner
      (fun it' b => IterationT.mapH
        (match · with
          | none => .skip ⟨it'⟩ ⟨⟩
          | some c => .yield ⟨it'⟩ c ⟨⟩) (f b))
      (fun it' => pure <| .skip ⟨it'⟩ ⟨⟩)
      (pure <| .done ⟨⟩)

instance {f : β → IterationT m γ} : SimpleIterator (MapMH α f) m γ :=
  inferInstanceAs <| SimpleIterator (FilterMapMH α _) m γ

-- TODO: This proof needs to use internals of IterationT instead of relying on successor_yield etc.
instance [Finite α m] : SimpleIterator.Finite (FilterMapMH α f) m where
  rel := InvImage FiniteIteratorWF.lt (finiteIteratorWF (m := m) ∘ FilterMapMH.inner)
  wf := InvImage.wf _ Finite.wf
  subrelation {it it'} h := by
    obtain ⟨_, _, hy, h⟩ | ⟨_, hs, h⟩ | ⟨hd, h⟩ := successor_matchStepH h
    · simp only [IterationT.mapH, Function.comp_apply] at h
      obtain ⟨h, hb, a, rfl, h'⟩ := h
      split at hb
      · cases hb
        apply Or.inl ⟨_, hy⟩
      · cases hb
        apply Or.inl ⟨_, hy⟩
    · cases successor_skip.mp h
      exact Or.inr hs
    · cases successor_done.mp h

instance {f : β → IterationT m γ} [Finite α m] : Finite (MapMH α f) m :=
  inferInstanceAs <| Finite (FilterMapMH α _) m

instance {f : β → IterationT m γ} [Productive α m] : SimpleIterator.Productive (MapMH α f) m where
  rel := InvImage ProductiveIteratorWF.lt (productiveIteratorWF (m := m) ∘ FilterMapMH.inner)
  wf := InvImage.wf _ Productive.wf
  subrelation {it it'} h := by
    simp only [SimpleIterator.step] at h
    obtain ⟨_, _, hy, h⟩ | ⟨_, hs, h⟩ | ⟨hd, h⟩ := property_matchStepH h
    · simp only [IterationT.mapH] at h
      obtain ⟨c, h, h'⟩ := h
      split at h
      · simp [Functor.map] at h'
      · cases h
    · cases h
      exact hs
    · cases h

@[always_inline, inline]
def Iterator.filterMapMH [Monad m] [Iterator α m β] (f : β → IterationT m (Option γ)) (it : α) :
    FilterMapMH α (m := m) f :=
  ⟨it⟩

@[always_inline, inline]
def Iterator.mapMH [Monad m] [Iterator α m β] (f : β → IterationT m γ) (it : α) :
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
def Iter.filterMapMH [Monad m] {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (f : β → CodensityT m (Option γ))
    (it : Iter (α := α) m β) :=
  ((toIter m <| Iterator.filterMapMH (m := m) (monadLift <| f ·) it.inner) : Iter m γ)

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
def Iter.mapMH [Monad m] {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (f : β → CodensityT m γ) (it : Iter (α := α) m β) :=
  (toIter m <| Iterator.mapMH (m := m) (monadLift <| f ·) it.inner : Iter m γ)

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
def Iter.filterMH [Monad m] {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (f : β → CodensityT m Bool) (it : Iter (α := α) m β) :=
  it.filterMapMH (fun b => (f b).mapH (if · then some b else none))

end FilterMapMH

section FilterMapH

universe u' v' u v

variable {α : Type u} {β : Type v} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    {γ : Type v'} {f : β → Option γ}

@[inline]
def Iter.filterMapH [Monad m] {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (f : β → Option γ) (it : Iter (α := α) m β) :=
  (it.filterMapMH (pure ∘ f) : Iter m γ)

@[inline]
def Iter.mapH [Monad m] {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (f : β → γ) (it : Iter (α := α) m β) :=
  (it.mapMH (pure ∘ f) : Iter m γ)

end FilterMapH

section FilterMap

variable {m : Type w → Type w'} {α : Type u} {β : Type v} {γ : Type w} {f : β → Option γ}

-- Potential other formulation of iterators: Each iterator type comes with equivalences for all types of the current level.
-- Then the following operations could be stated in higher generality, not requiring y : Type w.

@[inline]
def Iter.filterMap {_ : Iterator α m β} {_ : ComputableSmall.{w} α} [Monad m] (f : β → Option γ) (it : Iter (α := α) m β) :=
  (it.filterMapH f : Iter m γ)

@[inline]
def Iter.map {_ : Iterator α m β} {_ : ComputableSmall.{w} α} [Monad m] (f : β → γ) (it : Iter (α := α) m β) :=
  (it.mapH f : Iter m γ)

@[inline]
def Iter.filter {_ : Iterator α m β} {_ : ComputableSmall.{w} α} [Monad m] (f : β → Bool) (it : Iter (α := α) m β) :=
  (it.filterMapH (fun b => if f b then some b else none) : Iter m β)

end FilterMap

section FilterMapM

variable {m : Type w → Type w'} {α : Type u} {β : Type v} {γ : Type w} {f : β → Option γ}

@[inline]
def Iter.filterMapM {_ : Iterator α m β} {_ : ComputableSmall.{w} α} [Monad m] (f : β → m (Option γ)) (it : Iter (α := α) m β) :=
  (it.filterMapMH (monadLift ∘ f) : Iter m γ)

@[inline]
def Iter.mapM {_ : Iterator α m β} {_ : ComputableSmall.{w} α} [Monad m] (f : β → m γ) (it : Iter (α := α) m β) :=
  (it.filterMapM (fun b => some <$> f b) : Iter m γ)

@[inline]
def Iter.filterM {_ : Iterator α m β} {_ : ComputableSmall.{w} α} [Monad m] (f : β → m (ULift Bool)) (it : Iter (α := α) m β) :=
  it.filterMapMH (fun b => CodensityT.eval (f b) |>.mapH (if ·.down then some b else none))

end FilterMapM
