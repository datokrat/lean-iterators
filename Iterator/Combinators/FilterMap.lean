/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Wrapper
import Iterator.AbstractIteration
import Iterator.IteratorMorphism

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

structure FilterMapMH (α : Type u) {β : Type v}
    {m : Type max u v → Type max u v} [Iterator α m β] {β' : Type v'} {n : Type max u u' v v' → Type max u u' v v'}
    (f : β → n (ULift (Option β')))
    (mf : ∀ ⦃δ : Type max u v⦄ ⦃δ' : Type max u v u' v'⦄, (δ → δ') → m δ → n δ') : Type max u u' v where
  inner : α

variable {α : Type u} {β : Type v} {m : Type max u v → Type max u v} [Monad m] [Iterator α m β]
    {β' : Type v'} {n : Type max u u' v v' → Type max u u' v v'} {f : β → n (ULift (Option β'))} [Monad n]
    {mf : ∀ ⦃δ : Type max u v⦄ ⦃δ' : Type max u v u' v'⦄, (δ → δ') → m δ → n δ'}

instance : Iterator (FilterMapMH.{u'} α f mf) n β' :=
  Iteration.instIterator fun it =>
    matchStepH.{max u' v'} (fun {δ δ'} => mf (δ := δ) (δ' := δ')) it.inner
      (fun it' b => do match (← monadLift (f b)).down with
        | none => pure <| .skip ⟨it'⟩ ⟨⟩
        | some c => pure <| .yield ⟨it'⟩ c ⟨⟩)
      (fun it' => pure <| .skip ⟨it'⟩ ⟨⟩)
      (pure <| .done ⟨⟩)

instance [Finite α] : Finite (FilterMapMH.{u'} α f mf) := by
  refine finite_instIterator (α := FilterMapMH.{u'} α f mf) (β := β') (m := n) (rel := ?_) ?_ ?_ ?_
  · exact InvImage FiniteIteratorWF.lt (finiteIteratorWF ∘ FilterMapMH.inner)
  · apply InvImage.wf
    exact Finite.wf
  · intro it it' h
    replace h := prop_successor_matchStepH h
    obtain ⟨it'', b, h, h'⟩ | ⟨it'', h, h'⟩ | ⟨h, h'⟩ := h
    · simp only [Iteration.prop_map, Iteration.prop_bind] at h'
      obtain ⟨a, ha, b, h'⟩ := h'
      split at h'
      · cases up_successor_skip.mp ⟨a, ha, h'.1⟩
        apply Or.inl ⟨_, h⟩
      · cases up_successor_yield.mp ⟨a, ha, h'.1⟩
        apply Or.inl ⟨_, h⟩
    · cases up_successor_skip.mp h'
      exact Or.inr h
    · cases up_successor_done.mp h'
@[inline]
def Iterator.filterMapMH [Monad n] [Monad m] [Iterator α m β] (f : β → n (ULift (Option β'))) (mf : ∀ ⦃δ : Type max u v⦄ ⦃δ' : Type max u v u' v'⦄, (δ → δ') → m δ → n δ') (it : α) :
    FilterMapMH.{u'} α f mf :=
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
def Iter.filterMapMH [Monad n] [Monad m] [Iterator α m β] (f : β → n (ULift (Option β'))) (mf : ∀ ⦃δ : Type max u v⦄ ⦃δ' : Type max u v u' v'⦄, (δ → δ') → m δ → n δ') (it : Iter (α := α) m β) :
    Iter (α := FilterMapMH.{u'} α f mf) n β' :=
  toIter <| Iterator.filterMapMH f mf it.inner

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
def Iter.mapMH [Monad n] [Monad m] [Iterator α m β] (f : β → n (ULift β')) (mf : ∀ ⦃δ : Type max u v⦄ ⦃δ' : Type max u v u' v'⦄, (δ → δ') → m δ → n δ') (it : Iter (α := α) m β) :
    Iter (α := FilterMapMH.{u'} α (fun b => (ULift.up ∘ some ∘ ULift.down) <$> f b) mf) n β' :=
  it.filterMapMH _ mf


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
def Iter.filterMH {n : Type max u v u' → Type max u v u'} [Monad n] [Monad m] [Iterator α m β] (f : β → n (ULift Bool))
    (mf : ∀ ⦃δ : Type max u v⦄ ⦃δ' : Type max u v u'⦄, (δ → δ') → m δ → n δ') (it : Iter (α := α) m β) :
    Iter (α := FilterMapMH.{u'} α (fun b => (fun x => if x.down then (.up (some b)) else (.up none)) <$> f b) mf) n β :=
  it.filterMapMH _ mf

end FilterMapMH

section FilterMapH

universe u' v' u v

variable {α : Type u} {β : Type v} {m : Type max u v → Type max u v} [Monad m] [Iterator α m β]
    {β' : Type v'} {f : β → Option β'} {n : Type max u u' v v' → Type max u u' v v'} [Monad n]
    {mf : ∀ ⦃δ : Type max u v⦄ ⦃δ' : Type max u v u' v'⦄, (δ → δ') → m δ → n δ'}

@[inline]
def Iter.filterMapH [Monad n] [Monad m] [Iterator α m β] (f : β → Option β') (mf : ∀ ⦃δ : Type max u v⦄ ⦃δ' : Type max u v u' v'⦄, (δ → δ') → m δ → n δ') (it : Iter (α := α) m β) :=
  Iter.filterMapMH.{u', v'} (α := α) (m := m) (n := n) (fun b => pure <| .up <| f b) mf it

@[inline]
def Iter.mapH [Monad n] [Monad m] [Iterator α m β] (f : β → β') (mf : ∀ ⦃δ : Type max u v⦄ ⦃δ' : Type max u v u' v'⦄, (δ → δ') → m δ → n δ') (it : Iter (α := α) m β) :=
  Iter.filterMapH.{u', v'} (α := α) (fun b => some <| f b) mf it

end FilterMapH

section FilterMap

variable {m : Type max u v → Type max u v} {α : Type u} {β γ : Type v} {f : β → Option γ}

@[inline]
def Iter.filterMap [Iterator α m β] [Monad m] (f : β → Option γ) (it : Iter (α := α) m β) :=
  it.filterMapH f (m := m) (fun ⦃_ _⦄ => Functor.map)

@[inline]
def Iter.map [Iterator α m β] [Monad m] (f : β → γ) (it : Iter (α := α) m β) :=
  it.filterMap (some ∘ f)

@[inline]
def Iter.filter [Iterator α m β] [Monad m] (f : β → Bool) (it : Iter (α := α) m β) :=
  it.filterMap (fun b => if f b then some b else none)

end FilterMap

section FilterMapM

-- TODO: → Type v
variable {m : Type u → Type u} {α β γ : Type u} {f : β → Option γ}

@[inline]
def Iter.filterMapM [Iterator α m β] [Monad m] (f : β → m (Option γ)) (it : Iter (α := α) m β) :=
  Iter.filterMapMH.{u, u, u, u} (α := α) (fun b => ULift.up <$> f b) (m := m) (fun ⦃_ _⦄ => Functor.map) it

@[inline]
def Iter.mapM [Iterator α m β] [Monad m] (f : β → m γ) (it : Iter (α := α) m β) :=
  it.filterMapM (fun b => some <$> f b)

@[inline]
def Iter.filterM [Iterator α m β] [Monad m] (f : β → m (ULift Bool)) (it : Iter (α := α) m β) :=
  it.filterMapM (fun b => (if ·.down then some b else none) <$> f b)

end FilterMapM
