/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Combinators.FilterMap

/-!
This file provides the `flatMap` iterator and variants of it.

To each output of some base iterator `it`, `it.flatMap f`, applies `f` to obtain an inner iterator.
The `flatMap` iterator will yield all of the outputs of such an inner iterator before making the
next step with `it`. In other words, `it` flattens the iterator of iterators obtained by mapping with `f`.

Several variants of `flatMap` are provided:

* `H` suffix: heterogeneous variant that allows switching the monad and the universes.
* `D` suffix: dependently typed mapping function
-/

section ULiftState

universe u' v u

variable {α : Type u} {β : Type v}
  {m : Type (max u v) → Type (max u v)}
  {n : Type (max u v u') → Type (max u v u')}
  {f : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → n δ'}

structure IterULiftState (α : Type u) (f : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → n δ') : Type (max u u') where
  down : α

@[inline]
def IterULiftState.up (it : α) (f : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → n δ') : IterULiftState.{u'} α f :=
  ⟨it⟩

instance [Monad n] [Iterator α m β] : Iterator (IterULiftState.{u'} α f) n β where
  yielded it it' b := Iterator.yielded it.down it'.down b
  skipped it it' := Iterator.skipped it.down it'.down
  finished it := Iterator.finished it.down
  step it := do
    let s ← f ULift.up.{u'} (Iterator.step it.down)
    return match s.down with
    | .yield it' b h => .yield ⟨it'⟩ b h
    | .skip it' h => .skip ⟨it'⟩ h
    | .done h => .done h

def IterULiftState.downMorphism [Monad n] [Iterator α m β] :
    IteratorMorphism (IterULiftState.{u'} α f) α where
  mapIterator := IterULiftState.down
  mapValue := id
  preserves_yielded := Iff.rfl
  preserves_skipped := Iff.rfl
  preserves_finished := Iff.rfl

def Iter.uLiftState [Monad n] [Iterator α m β] (f : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → n δ') (it : Iter (α := α) m β) :
    Iter (α := IterULiftState.{u', v, u} α f) n β :=
  toIter ⟨it.inner⟩

instance [Monad n] [Iterator α m β] [Finite α] : Finite (IterULiftState.{u'} α f) :=
  IterULiftState.downMorphism.pullbackFinite

end ULiftState

section FlatMap

section FlattenDef

universe u v

variable {α α': Type (max u v)} {β : Type v}
  {m : Type (max u v) → Type (max u v)}
  [Iterator α m α'] [Iterator α' m β]

structure Flatten (α : Type max u v) {α' : Type max u v} {m : Type max u v → Type max u v} [Iterator α m α'] where
  it₁ : α
  it₂ : Option α'

@[inline]
def Flatten.init {α α' : Type max u v} {m : Type max u v → Type max u v} [Iterator α m α'] (it : α) : Flatten.{u, v} α :=
  ⟨it, none⟩

@[inline]
def flattenStepNone [Monad m] [Iterator α m α'] [Iterator α' m β] (it₁ : α) :
    Iteration m (RawStep (Flatten.{u, v} α) β) :=
  matchStep it₁
    (fun it₁' b => pure <| .skip { it₁ := it₁', it₂ := some b } ⟨⟩)
    (fun it₁' => pure <| .skip { it₁ := it₁', it₂ := none } ⟨⟩)
    (pure <| .done ⟨⟩)

variable (f) in
@[inline]
def flattenStepSome [Monad m] [Iterator α m α'] [Iterator α' m β] (it₁ : α) (it₂ : α') :
    Iteration m (RawStep (Flatten.{u, v} α) β) :=
  matchStep.{max u v, v} it₂
    (fun it₂' b => pure <| .yield { it₁ := it₁, it₂ := some it₂' } b ⟨⟩)
    (fun it₂' => pure <| .skip { it₁ := it₁, it₂ := some it₂' } ⟨⟩)
    (flattenStepNone it₁)

instance [Monad m] [Iterator α m α'] [Iterator α' m β] : Iterator (Flatten.{u, v} α) m β :=
  Iteration.instIterator fun
    | { it₁, it₂ := none } => flattenStepNone it₁
    | { it₁, it₂ := some it₂ } => flattenStepSome it₁ it₂

@[inline]
def Iter.flatten [Monad m] [i₁ : Iterator α m α'] [i₂ : Iterator α' m β] (it : Iter (α := α) m α') :=
  toIter <| Flatten.init it.inner

end FlattenDef

section Finite

universe u v

variable {α α' : Type max u v} {β : Type v} {m : Type max u v → Type max u v}

def Flatten.lex [Iterator α m α'] (r₁ : α → α → Prop) (r₂ : α' → α' → Prop) : Flatten.{u, v} α → Flatten.{u, v} α → Prop :=
  InvImage (Prod.Lex r₁ (Option.lt r₂)) (fun it => (it.it₁, it.it₂))

theorem Flatten.lex_of_left [Iterator α m α'] {r₁ : α → α → Prop} {r₂ : α' → α' → Prop} {it it'}
    (h : r₁ it'.it₁ it.it₁) : Flatten.lex.{u, v} r₁ r₂ it' it :=
  Prod.Lex.left _ _ h

theorem Flatten.lex_of_right [Iterator α m α'] {r₁ : α → α → Prop} {r₂ : α' → α' → Prop} {it₁ it₂ it₂'}
    (h : r₂ it₂' it₂) : Flatten.lex.{u, v} r₁ r₂ ⟨it₁, it₂'⟩ ⟨it₁, it₂⟩ :=
  Prod.Lex.right _ h

def rel [Iterator α m α'] [Iterator α' m β] : Flatten.{u, v} α → Flatten.{u, v} α → Prop :=
  Flatten.lex (InvImage FiniteIteratorWF.lt finiteIteratorWF) (InvImage FiniteIteratorWF.lt finiteIteratorWF)

set_option pp.universes true in
theorem descending_flattenStepNone
    [Monad m] [Iterator α m α'] [Iterator α' m β] {it₁ : α} {it' : Flatten α}
    (h : ((ULift.up.{v} ∘ IterStep.successor) <$> flattenStepNone it₁).prop (ULift.up <| some it')) :
    (finiteIteratorWF (m := m) it'.it₁).lt (finiteIteratorWF it₁) := by
  simp only [flattenStepNone] at h
  have := prop_successor_matchStep h
  obtain ⟨it'', b, hy, h⟩ | ⟨it'', hs, h⟩ | ⟨hd, h⟩ := this
  · cases up_successor_skip.mp h
    exact Or.inl ⟨_, hy⟩
  · cases up_successor_skip.mp h
    exact Or.inr hs
  · cases up_successor_done.mp h

theorem descending_flattenStepSome
    [Monad m] [Iterator α m α'] [Iterator α' m β] {it₁ : α} {it₂ : α'} {it' : Flatten α}
    (h : ((ULift.up.{v} ∘ IterStep.successor) <$> flattenStepSome it₁ it₂).prop (ULift.up <| some it')) :
    rel it' { it₁ := it₁, it₂ := some it₂ } := by
  simp only [flattenStepSome] at h
  obtain ⟨it', b, hy, h⟩ | ⟨it', hs, h⟩ | ⟨hd, h⟩ := prop_successor_matchStep h
  · cases up_successor_yield.mp h
    apply Flatten.lex_of_right
    exact Or.inl ⟨_, hy⟩
  · cases up_successor_skip.mp h
    apply Flatten.lex_of_right
    exact Or.inr hs
  · apply Flatten.lex_of_left
    exact descending_flattenStepNone h

-- TODO: put this into core
theorem Option.wellFounded_lt {α} {rel : α → α → Prop} (h : WellFounded rel) : WellFounded (Option.lt rel) := by
  refine ⟨?_⟩
  intro x
  have hn : Acc (Option.lt rel) none := by
    refine Acc.intro none ?_
    intro y hyx
    cases y <;> cases hyx
  cases x
  · exact hn
  · rename_i x
    induction h.apply x
    rename_i x' h ih
    refine Acc.intro _ ?_
    intro y hyx'
    cases y
    · exact hn
    · exact ih _ hyx'

instance [Monad m] [Iterator α m α'] [Iterator α' m β] [Finite α] [Finite α'] :
    Finite (Flatten α) := by
  refine finite_instIterator (m := m) _ (rel := rel) ?_ ?_
  · simp only [rel, Flatten.lex]
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact InvImage.wf _ Finite.wf
    · exact Option.wellFounded_lt <| InvImage.wf _ Finite.wf
  · intro it it' h
    split at h
    · apply Flatten.lex_of_left
      exact descending_flattenStepNone h
    · exact descending_flattenStepSome h

end Finite

section General

section FlatMapH

variable {α : Type u} {β : Type v} {m : Type max u v → Type max u v} [Monad m]
  {α' : Type u'} {β' : Type v'} {n : Type max u' v' → Type max u' v'} [Monad n]
  {p : Type max u v u' v' → Type max u v u' v'} [Monad p]
  {fm : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → p δ'} {fn : ∀ ⦃δ δ'⦄, (δ → δ') → n δ → p δ'}
  {f : (b : β) → α'}

/--
Given an iterator `it`, a heterogeneous iterator-valued mapping function `f`
and monad transformations `fm` and `fn`, `it.flatMapH f mf` is an iterator that applies
`f` to each output of `it` to obtain an inner iterator.
The `flatMap` iterator will yield all of the outputs of such an inner iterator before making the
next step with `it`. In other words, `it` flattens the iterator of iterators obtained by mapping with `f`.

**Marble diagram:**

```text
it                 ---a    ---b     c    --d--⊥
f a                   a1-a2⊥
f b                           b1-b2 ⊥
f c                                 c1-c2⊥
f d                                        ⊥
it.flatMapH        ---a1-a2---b1-b2 c1-c2  ---⊥
```

Note that it is always possible for the implementation to insert some skip steps in between.
The insertion of additional skip steps is an implementation detail and should not be relevant
for any consumer.

**Termination properties:**

* `Finite` instance: only if `it` and all of the iternal iterators are finite
* `Productive` instance: only if `it` it finite and all of the internal iterators are productive

_TODO:_ implement the `Productive` instance

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it` or an internal stream.

_TODO_: Improve this so that the cost is only incurred with each output of `it`. This should at
least work for internal iterator types that contain a computationally cheap empty iterator.
-/
@[inline]
def Iter.flatMapH (f : β → α') [Iterator α m β] (it : Iter (α := α) m β) [Iterator α' n β'] [Monad m] [Monad n] [Monad p]
    (fm : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → p δ') (fn : ∀ ⦃δ δ'⦄, (δ → δ') → n δ → p δ') :=
  it.mapH (fun b => IterULiftState.up.{max u v u' v'} (f b) fn) fm |>.flatten

end FlatMapH

section Dependent

universe v u

structure SigmaIterator (β : Type u) (α : β → Type max u v) where
  b : β
  inner : α b

def SigmaIterator.lex {β : Type u} {α : β → Type max u v} (r : (b : β) → α b → α b → Prop) : SigmaIterator β α → SigmaIterator β α → Prop :=
  InvImage (PSigma.Lex emptyRelation r) (fun it => ⟨it.b, it.inner⟩)

theorem SigmaIterator.lex_of_right {β : Type u} {α : β → Type max u v} (r : (b : β) → α b → α b → Prop) {b it it'}
    (h : r b it it') : SigmaIterator.lex r ⟨b, it⟩ ⟨b, it'⟩ :=
  PSigma.Lex.right _ h

def SigmaIterator.rel {β : Type u} {α : β → Type max u v} [∀ b, Iterator (α b) m β'] :
    SigmaIterator β α → SigmaIterator β α → Prop :=
  SigmaIterator.lex (fun _ => InvImage FiniteIteratorWF.lt finiteIteratorWF)

instance {β : Type u} {α : β → Type max u v} {γ : Type w}
    {m : Type max u v w → Type max u v w} [Monad m]
    [i : ∀ b, Iterator (α b) m γ] : Iterator (SigmaIterator β α) m γ :=
  Iteration.instIterator fun it => do
    matchStep it.inner
      (fun it' c => pure <| .yield ⟨it.b, it'⟩ c ⟨⟩)
      (fun it' => pure <| .skip ⟨it.b, it'⟩ ⟨⟩)
      (pure <| .done ⟨⟩)

instance {β : Type u} {α : β → Type max u v} {γ : Type w}
    {m : Type max u v w → Type max u v w} [Monad m]
    [∀ b, Iterator (α b) m γ] [∀ b, Finite (α b)] : Finite (SigmaIterator β α) := by
  refine finite_instIterator _ (rel := ?_) ?_ ?_
  · exact SigmaIterator.rel
  · rw [SigmaIterator.rel]
    apply InvImage.wf
    refine ⟨fun ⟨b, it⟩ => ?_⟩
    apply PSigma.lexAccessible
    · exact emptyWf.wf.apply b
    · intro a
      apply InvImage.wf
      exact Finite.wf
  · intro it it' h
    obtain ⟨_, _, hy, h⟩ | ⟨_, hs, h⟩ | ⟨hd, h⟩ := prop_successor_matchStep h
    · cases up_successor_yield.mp h
      apply SigmaIterator.lex_of_right
      exact Or.inl ⟨_, hy⟩
    · cases up_successor_skip.mp h
      apply SigmaIterator.lex_of_right
      exact Or.inr hs
    · cases up_successor_done.mp h

variable {α : Type u} {β : Type v} {m : Type max u v → Type max u v} [Monad m]
  {α' : β → Type u'} {β' : Type v'} {n : Type max u' v' → Type max u' v'} [Monad n]
  {p : Type max u v u' v' → Type max u v u' v'} [Monad p]
  {fm : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → p δ'} {fn : ∀ ⦃δ δ'⦄, (δ → δ') → n δ → p δ'}
  {f : (b : β) → α' b}

/--
Given an iterator `it`, a dependently typed, heterogeneous iterator-valued mapping function `f`
and monad transformations `fm` and `fn`, `it.flatMapHD f mf` is an iterator that applies
`f` to each output of `it` to obtain an inner iterator.
The `flatMap` iterator will yield all of the outputs of such an inner iterator before making the
next step with `it`. In other words, `it` flattens the iterator of iterators obtained by mapping with `f`.

**Marble diagram:**

```text
it                 ---a    ---b     c    --d--⊥
f a                   a1-a2⊥
f b                           b1-b2 ⊥
f c                                 c1-c2⊥
f d                                        ⊥
it.flatMapHD       ---a1-a2---b1-b2 c1-c2  ---⊥
```

Note that it is always possible for the implementation to insert some skip steps in between.
The insertion of additional skip steps is an implementation detail and should not be relevant
for any consumer.

**Termination properties:**

* `Finite` instance: only if `it` and all of the iternal iterators are finite
* `Productive` instance: only if `it` it finite and all of the internal iterators are productive

_TODO:_ implement the `Productive` instance

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it` or an internal stream.

_TODO_: Improve this so that the cost is only incurred with each output of `it`. This should at
least work for internal iterator types that contain a computationally cheap empty iterator.
-/
@[inline]
def Iter.flatMapHD (f : (b : β) → α' b) [Iterator α m β] (it : Iter (α := α) m β) [∀ b, Iterator (α' b) n β'] [Monad m] [Monad n] [Monad p]
    (fm : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → p δ') (fn : ∀ ⦃δ δ'⦄, (δ → δ') → n δ → p δ') :=
  it.mapH (fun b => SigmaIterator.mk.{max u v u' v'} b (IterULiftState.up.{max u v u' v', v', u'} (f b) fn)) fm |>.flatten

end Dependent

section Simple

/--
Given an iterator `it`, an iterator-valued mapping function `f`,
`it.flatMap f` is an iterator that applies `f` to each output of `it` to obtain an inner iterator.
The `flatMap` iterator will yield all of the outputs of such an inner iterator before making the
next step with `it`. In other words, `it` flattens the iterator of iterators obtained by mapping with `f`.

**Marble diagram:**

```text
it                 ---a    ---b     c    --d--⊥
f a                   a1-a2⊥
f b                           b1-b2 ⊥
f c                                 c1-c2⊥
f d                                        ⊥
it.flatMap         ---a1-a2---b1-b2 c1-c2  ---⊥
```

Note that it is always possible for the implementation to insert some skip steps in between.
The insertion of additional skip steps is an implementation detail and should not be relevant
for any consumer.

**Termination properties:**

* `Finite` instance: only if `it` and all of the iternal iterators are finite
* `Productive` instance: only if `it` it finite and all of the internal iterators are productive

_TODO:_ implement the `Productive` instance

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it` or an internal stream.

_TODO_: Improve this so that the cost is only incurred with each output of `it`. This should at
least work for internal iterator types that contain a computationally cheap empty iterator.
-/
@[inline]
def Iter.flatMap {α : Type u} {β : Type v} {m : Type max u v → Type max u v} [Monad m] [Iterator α m β]
    {α' : Type u} {β' : Type v} [Iterator α' m β'] (f : β → α') (it : Iter (α := α) m β) :=
  Iter.flatMapH.{u, v, u, v} f it (fun ⦃_ _⦄ => Functor.map) (fun ⦃_ _⦄ => Functor.map)

/--
Given an iterator `it`, an iterator-valued mapping function `f`,
`it.flatMapD f` is an iterator that applies `f` to each output of `it` to obtain an inner iterator.
The `flatMap` iterator will yield all of the outputs of such an inner iterator before making the
next step with `it`. In other words, `it` flattens the iterator of iterators obtained by mapping with `f`.

**Marble diagram:**

```text
it                 ---a    ---b     c    --d--⊥
f a                   a1-a2⊥
f b                           b1-b2 ⊥
f c                                 c1-c2⊥
f d                                        ⊥
it.flatMapD        ---a1-a2---b1-b2 c1-c2  ---⊥
```

Note that it is always possible for the implementation to insert some skip steps in between.
The insertion of additional skip steps is an implementation detail and should not be relevant
for any consumer.

**Termination properties:**

* `Finite` instance: only if `it` and all of the iternal iterators are finite
* `Productive` instance: only if `it` it finite and all of the internal iterators are productive

_TODO:_ implement the `Productive` instance

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it` or an internal stream.

_TODO_: Improve this so that the cost is only incurred with each output of `it`. This should at
least work for internal iterator types that contain a computationally cheap empty iterator.
-/
@[inline]
def Iter.flatMapD {α : Type u} {β : Type v} {m : Type max u v → Type max u v} [Monad m] [Iterator α m β]
    {α' : β → Type u} {β' : Type v} [∀ b, Iterator (α' b) m β'] (f : (b : β) → α' b) (it : Iter (α := α) m β) :=
  -- TODO: get universes into the right order
  Iter.flatMapHD.{v, u, u, v} (β := β) f it (fun ⦃_ _⦄ => Functor.map) (fun ⦃_ _⦄ => Functor.map) (n := m) (p := m)

end Simple

end General

end FlatMap
