/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.SimpleIterator

section ZipH

universe u₁ u₂ v₁ v₂ w₁ w₂ w₃

variable {m : Type w → Type w'}
  {α₁ : Type u₁} {β₁ : Type v₁} [Iterator α₁ m β₁]
  {α₂ : Type u₂} {β₂ : Type v₂} [Iterator α₂ m β₂]

structure ZipH (α₁ : Type u₁) (β₁ : Type v₁) (α₂ : Type u₂) where
  left : α₁
  memoizedLeft : Option β₁
  right : α₂

instance [Iterator α₁ m β₁] [Iterator α₂ m β₂] [Monad m] :
    SimpleIterator (ZipH α₁ β₁ α₂) m (β₁ × β₂) where
  step it :=
    match it.memoizedLeft with
    | none =>
      matchStepH it.left
        (fun it₁' b₁ => pure <| .skip ⟨it₁', some b₁, it.right⟩)
        (fun it₁' => pure <| .skip ⟨it₁', none, it.right⟩)
        (pure <| .done)
    | some b₁ =>
      matchStepH it.right
        (fun it₂' b₂ => pure <| .yield ⟨it.left, none, it₂'⟩ (b₁, b₂))
        (fun it₂' => pure <| .skip ⟨it.left, some b₁, it₂'⟩)
        (pure <| .done)

@[inline]
def Iter.zipH [Monad m] [ComputableUnivLE.{max u₁ u₂ v₁, w}]
    {small₁ : ComputableSmall.{w} α₁} {small₂ : ComputableSmall.{w} α₂}
    (left : Iter (α := α₁) m β₁ (small := small₁)) (right : Iter (α := α₂) m β₂ (small := small₂)) :
    Iter (α := ZipH α₁ β₁ α₂) m (β₁ × β₂) :=
  toIter m ⟨left.inner, none, right.inner⟩

-- TODO: put this into core. This is also duplicated in FlatMap
theorem ZipH.wellFounded_optionLt {α} {rel : α → α → Prop} (h : WellFounded rel) :
    WellFounded (Option.lt rel) := by
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

variable (m) in
def ZipH.rel₁ : ZipH α₁ β₁ α₂ → ZipH α₁ β₁ α₂ → Prop :=
  InvImage (Prod.Lex
      FiniteIteratorWF.lt
      (Prod.Lex (Option.lt emptyRelation) ProductiveIteratorWF.lt))
    (fun it => (finiteIteratorWF it.left (m := m), (it.memoizedLeft, productiveIteratorWF (m := m) it.right)))

theorem ZipH.rel₁_of_left {it' it : ZipH α₁ β₁ α₂}
    (h : (finiteIteratorWF it'.left (m := m)).lt (finiteIteratorWF it.left)) : ZipH.rel₁ m it' it :=
  Prod.Lex.left _ _ h

theorem ZipH.rel₁_of_memoizedLeft {left : α₁} {b' b : Option β₁} {right' right : α₂}
    (h : Option.lt emptyRelation b' b) :
    ZipH.rel₁ m ⟨left, b', right'⟩ ⟨left, b, right⟩ :=
  Prod.Lex.right _ <| Prod.Lex.left _ _ h

theorem ZipH.rel₁_of_right {left : α₁} {b : Option β₁} {it' it : α₂}
    (h : (productiveIteratorWF it' (m := m)).lt (productiveIteratorWF it)) :
    ZipH.rel₁ m ⟨left, b, it'⟩ ⟨left, b, it⟩ :=
  Prod.Lex.right _ <| Prod.Lex.right _ h

instance [Monad m] [Finite α₁ m] [Productive α₂ m] :
    SimpleIterator.Finite (ZipH α₁ β₁ α₂) m where
  rel := ZipH.rel₁ m
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact WellFoundedRelation.wf
    · refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
      · apply ZipH.wellFounded_optionLt
        exact emptyWf.wf
      · exact Productive.wf
  subrelation {it it'} h := by
    obtain ⟨left, b, right⟩ := it
    dsimp only [SimpleIterator.step] at h
    split at h
    · obtain ⟨_, _, hy, h⟩ | ⟨_, hs, h⟩ | ⟨hd, h⟩ := successor_matchStepH h
      · cases successor_skip.mp h
        apply ZipH.rel₁_of_left
        exact Or.inl ⟨_, hy⟩
      · cases successor_skip.mp h
        apply ZipH.rel₁_of_left
        exact Or.inr hs
      · cases successor_done.mp h
    · obtain ⟨_, _, hy, h⟩ | ⟨_, hs, h⟩ | ⟨hd, h⟩ := successor_matchStepH h
      · cases successor_yield.mp h
        apply ZipH.rel₁_of_memoizedLeft
        trivial
      · cases successor_skip.mp h
        apply ZipH.rel₁_of_right
        exact hs
      · cases successor_done.mp h

def ZipH.lt_with_top {α} (r : α → α → Prop) : Option α → Option α → Prop
  | none, _ => false
  | some _, none => true
  | some a', some a => r a' a

theorem ZipH.wellFounded_lt_with_top {α} {r : α → α → Prop} (h : WellFounded r) :
    WellFounded (lt_with_top r) := by
  refine ⟨?_⟩
  intro x
  constructor
  intro x' hlt
  match x' with
  | none => contradiction
  | some x' =>
    clear hlt
    induction h.apply x'
    rename_i ih
    constructor
    intro x'' hlt'
    match x'' with
    | none => contradiction
    | some x'' => exact ih x'' hlt'

variable (m) in
def ZipH.rel₂ : ZipH α₁ β₁ α₂ → ZipH α₁ β₁ α₂ → Prop :=
  InvImage (Prod.Lex
      FiniteIteratorWF.lt
      (Prod.Lex (ZipH.lt_with_top emptyRelation) ProductiveIteratorWF.lt))
    (fun it => (finiteIteratorWF it.right (m := m), (it.memoizedLeft, productiveIteratorWF it.left (m := m))))

theorem ZipH.rel₂_of_right {it' it : ZipH α₁ β₁ α₂}
    (h : (finiteIteratorWF it'.right).lt (finiteIteratorWF it.right (m := m))) : ZipH.rel₂ m it' it :=
  Prod.Lex.left _ _ h

theorem ZipH.rel₂_of_memoizedLeft {left' left : α₁} {b' b : Option β₁} {right : α₂}
    (h : ZipH.lt_with_top emptyRelation b' b) :
    ZipH.rel₂ m ⟨left', b', right⟩ ⟨left, b, right⟩ :=
  Prod.Lex.right _ <| Prod.Lex.left _ _ h

theorem ZipH.rel₂_of_left {left' left : α₁} {b : Option β₁} {right : α₂}
    (h : (productiveIteratorWF left' (m := m)).lt (productiveIteratorWF left)) :
    ZipH.rel₂ m ⟨left', b, right⟩ ⟨left, b, right⟩ :=
  Prod.Lex.right _ <| Prod.Lex.right _ h

instance [Monad m] [Productive α₁ m] [Finite α₂ m] :
    SimpleIterator.Finite (ZipH α₁ β₁ α₂) m where
  rel := ZipH.rel₂ m
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact WellFoundedRelation.wf
    · refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
      · apply ZipH.wellFounded_lt_with_top
        exact emptyWf.wf
      · exact Productive.wf
  subrelation {it it'} h := by
    obtain ⟨left, b, right⟩ := it
    dsimp only [SimpleIterator.step] at h
    split at h
    · obtain ⟨_, _, hy, h⟩ | ⟨_, hs, h⟩ | ⟨hd, h⟩ := successor_matchStepH h
      · cases successor_skip.mp h
        apply ZipH.rel₂_of_memoizedLeft
        trivial
      · cases successor_skip.mp h
        apply ZipH.rel₂_of_left
        exact hs
      · cases successor_done.mp h
    · obtain ⟨_, _, hy, h⟩ | ⟨_, hs, h⟩ | ⟨hd, h⟩ := successor_matchStepH h
      · cases successor_yield.mp h
        apply ZipH.rel₂_of_right
        exact Or.inl ⟨_, hy⟩
      · cases successor_skip.mp h
        apply ZipH.rel₂_of_right
        exact Or.inr <| hs
      · cases successor_done.mp h

end ZipH

-- TODO: Does it make sense to have this specialized version?
section Zip

universe u v

variable {α₁ α₂ : Type u} {β₁ β₂ : Type v} {m : Type w → Type w'}
  [Monad m] [Iterator α₁ m β₁] [Iterator α₂ m β₂]

/--
Given two iterators `left` and `right`,
`left.zip right` is an iterator that yields pairs of outputs of `left` and `right` as long as
both produce outputs. When one of them terminates, the `zip` iterator will also terminate.

**Marble diagram:**

```text
left               --a        ---b        --c
right                 --x         --y        --⊥
left.zip right     -----(a, x)------(b, y)-----⊥
```

Note that it is always possible for the implementation to insert some skip steps in between.
The insertion of additional skip steps is an implementation detail and should not be relevant
for any consumer.

**Termination properties:**

* `Finite` instance: only if either `left` or `right` is finite and the other is productive
* `Productive` instance: only if `left` and `right` are productive

_TODO:_ implement the `Productive` instance

**Performance:**

This combinator incurs an additional O(1) cost with each output of `left` or `right`.
-/
def Iter.zip {small₁ : ComputableSmall.{w} α₁} {small₂ : ComputableSmall.{w} α₂} [ComputableUnivLE.{max u v}]
    (left : Iter (α := α₁) m β₁ (small := small₁)) (right : Iter (α := α₂) m β₂ (small := small₂)) :=
  (Iter.zipH left right : Iter m (β₁ × β₂))

end Zip
