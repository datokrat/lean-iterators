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

structure FilterMapMH (α : Type u) {β : Type v} (γ : Type v') {γ' : Type w} (γEquiv : Equiv γ γ')
    {m : Type w → Type w'} (f : β → m (Option γ')) where
  inner : α

variable {α : Type u} {β : Type v} {γ : Type v'} {γ' : Type w} {m : Type w → Type w'}
    [Monad m] [Iterator α m β]
    {γEquiv : Equiv γ γ'} {f : β → m (Option γ')}

instance : SimpleIterator (FilterMapMH α γ γEquiv f) m γ where
  α' := FilterMapMH (Iterator.α' α m) γ γEquiv f
  β' := γ'
  αEquiv := sorry
  βEquiv := γEquiv
  step it :=
    matchStep it.inner
      (fun it' b =>
        (match · with
          | none => .skip ⟨it'⟩ ⟨⟩
          | some c => .yield ⟨it'⟩ c ⟨⟩)
        <$> (monadLift (f b)))
      (fun it' => pure <| .skip ⟨it'⟩ ⟨⟩)
      (pure <| .done ⟨⟩)

-- TODO: This proof needs to use internals of IterationT instead of relying on successor_yield etc.
instance [Finite α m] : SimpleIterator.Finite (FilterMapMH α γ γEquiv f) m where
  rel := InvImage FiniteIteratorWF.lt (finiteIteratorWF (m := m) ∘ FilterMapMH.inner)
  wf := InvImage.wf _ Finite.wf
  subrelation {it it'} h := by
    obtain ⟨_, _, hy, h⟩ | ⟨_, hs, h⟩ | ⟨hd, h⟩ := successor_matchStep h
    · simp only [Functor.map, Function.comp_apply] at h
      obtain ⟨h, hb, a, rfl, h'⟩ := h
      split at hb
      · cases hb
        apply Or.inl ⟨_, hy⟩
      · cases hb
        apply Or.inl ⟨_, hy⟩
    · cases successor_skip.mp h
      exact Or.inr hs
    · cases successor_done.mp h

@[inline]
def Iterator.filterMapMH [Monad m] [Iterator α m β] (f : β → ContT m (Option γ') (Option γ)) (it : Iterator.α' α m) :
    FilterMapMH (Iterator.α' α m) γ γEquiv (fun b => f b (pure <| ·.map γEquiv.hom)) :=
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
def Iter.filterMapMH [Monad m] [Iterator α m β] (f : β → ContT m (Option γ') (Option γ)) (it : Iter (α := α) m β) :=
  ((toIter (α := FilterMapMH α γ γEquiv (fun b => f b (pure <| ·.map γEquiv.hom))) m <| Iterator.filterMapMH f it.inner) : Iter m γ)

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
def Iter.mapMH [Monad m] [Iterator α m β] (f : β → OverT m β') (it : Iter (α := α) m β) :=
  (it.filterMapMH (fun b => some <$> f b) : Iter m β')

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
def Iter.filterMH [Monad m] [Iterator α m β] (f : β → OverT m Bool) (it : Iter (α := α) m β) :
    Iter (α := FilterMapMH α (fun b => (f b).mapH (fun x => if x then some b else none))) m β :=
  (it.filterMapMH _ : Iter m β)

end FilterMapMH

section FilterMapH

universe u' v' u v

variable {α : Type u} {β : Type v} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    {β' : Type v'} {f : β → Option β'}

@[inline]
def Iter.filterMapH [Monad m] [Iterator α m β] (f : β → Option β') (it : Iter (α := α) m β) :=
  (it.filterMapMH (pure ∘ f) : Iter m β')

@[inline]
def Iter.mapH [Monad m] [Iterator α m β] (f : β → β') (it : Iter (α := α) m β) :=
  (it.filterMapH (some ∘ f) : Iter m β')

end FilterMapH

section FilterMap

variable {m : Type max u v → Type max u v} {α : Type u} {β γ : Type v} {f : β → Option γ}

@[inline]
def Iter.filterMap [Iterator α m β] [Monad m] (f : β → Option γ) (it : Iter (α := α) m β) :=
  (it.filterMapH f : Iter m γ)

@[inline]
def Iter.map [Iterator α m β] [Monad m] (f : β → γ) (it : Iter (α := α) m β) :=
  (it.filterMap (some ∘ f) : Iter m γ)

@[inline]
def Iter.filter [Iterator α m β] [Monad m] (f : β → Bool) (it : Iter (α := α) m β) :=
  (it.filterMap (fun b => if f b then some b else none) : Iter m β)

end FilterMap

section FilterMapM

variable {m : Type u → Type v} {α β γ : Type u} {f : β → Option γ}

@[inline]
def Iter.filterMapM [Iterator α m β] [Monad m] (f : β → m (Option γ)) (it : Iter (α := α) m β) :=
  (it.filterMapMH (OverT.eval ∘ f) : Iter m γ)

@[inline]
def Iter.mapM [Iterator α m β] [Monad m] (f : β → m γ) (it : Iter (α := α) m β) :=
  (it.filterMapM (fun b => some <$> f b) : Iter m γ)

@[inline]
def Iter.filterM [Iterator α m β] [Monad m] (f : β → m (ULift Bool)) (it : Iter (α := α) m β) :=
  (it.filterMapM (fun b => (if ·.down then some b else none) <$> f b) : Iter m β)

end FilterMapM
