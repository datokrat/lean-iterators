/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic
import Iterator.Consumers.Collect
import Iterator.Consumers.Loop

section ZipH

universe u₁ u₂ v₁ v₂ w₁ w₂ w₃

variable {m : Type w → Type w'}
  {α₁ : Type w} {β₁ : Type v₁} [Iterator α₁ m β₁]
  {α₂ : Type w} {β₂ : Type v₂} [Iterator α₂ m β₂]

structure ZipH (α₁ : Type w) (m : Type w → Type w') {β₁ : Type v₁} [Iterator α₁ m β₁] (α₂ : Type w) (β₂ : Type v₂) where
  left : Iter (α := α₁) m β₁
  memoizedLeft : USquash.{w} (Option { out : β₁ // ∃ it : Iter (α := α₁) m β₁, it.plausible_output out })
  right : Iter (α := α₂) m β₂

inductive ZipH.PlausibleStep (it : Iter (α := ZipH α₁ m α₂ β₂) m (β₁ × β₂)) :
    IterStep (Iter (α := ZipH α₁ m α₂ β₂) m (β₁ × β₂)) (β₁ × β₂) → Prop where
  | yieldLeft (hm : it.inner.memoizedLeft.inflate = none) {it' out} (hp : it.inner.left.plausible_step (.yield it' out)) :
      PlausibleStep it (.skip ⟨⟨it', .deflate (some ⟨out, _, _, hp⟩), it.inner.right⟩⟩)
  | skipLeft (hm : it.inner.memoizedLeft.inflate = none) {it'} (hp : it.inner.left.plausible_step (.skip it')) :
      PlausibleStep it (.skip ⟨⟨it', .deflate none, it.inner.right⟩⟩)
  | doneLeft (hm : it.inner.memoizedLeft.inflate = none) (hp : it.inner.left.plausible_step .done) :
      PlausibleStep it .done
  | yieldRight {out₁} (hm : it.inner.memoizedLeft.inflate = some out₁) {it₂' out₂} (hp : it.inner.right.plausible_step (.yield it₂' out₂)) :
      PlausibleStep it (.yield ⟨⟨it.inner.left, .deflate none, it₂'⟩⟩ (out₁, out₂))
  | skipRight {out₁} (hm : it.inner.memoizedLeft.inflate = some out₁) {it₂'} (hp : it.inner.right.plausible_step (.skip it₂')) :
      PlausibleStep it (.skip ⟨⟨it.inner.left, .deflate (some out₁), it₂'⟩⟩)
  | doneRight {out₁} (hm : it.inner.memoizedLeft.inflate = some out₁) (hp : it.inner.right.plausible_step .done) :
      PlausibleStep it .done

instance {it : Iter (α := ZipH α₁ m α₂ β₂) m (β₁ × β₂)} :
    Small.{w} (Subtype <| ZipH.PlausibleStep it) := sorry

instance ZipH.instIterator [Monad m] :
    Iterator (ZipH α₁ m α₂ β₂) m (β₁ × β₂) where
  plausible_step := PlausibleStep
  step_small := inferInstance
  step it :=
    match hm : it.inner.memoizedLeft.inflate with
    | none => do
      match (← it.inner.left.stepH).inflate with
      | .yield it₁' out hp =>
          pure <| .deflate <| .skip ⟨⟨it₁', .deflate (some ⟨out, _, _, hp⟩), it.inner.right⟩⟩ (.yieldLeft hm hp)
      | .skip it₁' hp =>
          pure <| .deflate <| .skip ⟨⟨it₁', .deflate none, it.inner.right⟩⟩ (.skipLeft hm hp)
      | .done hp =>
          pure <| .deflate <| .done (.doneLeft hm hp)
    | some out₁ => do
      match (← it.inner.right.stepH).inflate with
      | .yield it₂' out₂ hp =>
          pure <| .deflate <| .yield ⟨⟨it.inner.left, .deflate none, it₂'⟩⟩ (out₁, out₂) (.yieldRight hm hp)
      | .skip it₂' hp =>
          pure <| .deflate <| .skip ⟨⟨it.inner.left, .deflate (some out₁), it₂'⟩⟩ (.skipRight hm hp)
      | .done hp =>
          pure <| .deflate <| .done (.doneRight hm hp)

@[inline]
def Iter.zipH [Monad m]
    (left : Iter (α := α₁) m β₁) (right : Iter (α := α₂) m β₂) :
    Iter (α := ZipH α₁ m α₂ β₂) m (β₁ × β₂) :=
  toIter ⟨left, .deflate none, right⟩ m _

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
def ZipH.rel₁ [Finite α₁ m] [Productive α₂ m] :
    Iter (α := ZipH α₁ m α₂ β₂) m (β₁ × β₂) → Iter (α := ZipH α₁ m α₂ β₂) m (β₁ × β₂) → Prop :=
  InvImage (Prod.Lex
      Iter.TerminationMeasures.Finite.rel
      (Prod.Lex (Option.lt emptyRelation) Iter.TerminationMeasures.Productive.rel))
    (fun it => (it.inner.left.finitelyManySteps, (it.inner.memoizedLeft.inflate, it.inner.right.finitelyManySkips)))

theorem ZipH.rel₁_of_left [Finite α₁ m] [Productive α₂ m] {it' it : Iter (α := ZipH α₁ m α₂ β₂) m (β₁ × β₂)}
    (h : it'.inner.left.finitelyManySteps.rel it.inner.left.finitelyManySteps) : ZipH.rel₁ m it' it :=
  Prod.Lex.left _ _ h

theorem ZipH.rel₁_of_memoizedLeft [Finite α₁ m] [Productive α₂ m]
    {left : Iter (α := α₁) m β₁} {b' b} {right' right : Iter (α := α₂) m β₂}
    (h : Option.lt emptyRelation b'.inflate b.inflate) :
    ZipH.rel₁ m ⟨left, b', right'⟩ ⟨left, b, right⟩ :=
  Prod.Lex.right _ <| Prod.Lex.left _ _ (by simp only [USquash.inflate_deflate]; exact h)

theorem ZipH.rel₁_of_right [Finite α₁ m] [Productive α₂ m]
    {left : Iter (α := α₁) m β₁} {b b' : _} {it' it : Iter (α := α₂) m β₂}
    (h : b.inflate = b'.inflate)
    (h' : it'.finitelyManySkips.rel it.finitelyManySkips) :
    ZipH.rel₁ m ⟨left, b, it'⟩ ⟨left, b', it⟩ := by
  cases USquash.inflate.inj h
  exact Prod.Lex.right _ <| Prod.Lex.right _ h'

instance [Monad m] [Finite α₁ m] [Productive α₂ m] :
    FinitenessRelation (ZipH α₁ m α₂ β₂) m where
  rel := ZipH.rel₁ m
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact WellFoundedRelation.wf
    · refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
      · apply ZipH.wellFounded_optionLt
        exact emptyWf.wf
      · apply InvImage.wf
        exact Productive.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case yieldLeft hm it' out hp =>
      cases h
      apply ZipH.rel₁_of_left
      apply Iter.plausible_successor_of_yield
      exact hp
    case skipLeft hm it' hp =>
      cases h
      apply ZipH.rel₁_of_left
      apply Iter.plausible_successor_of_skip
      exact hp
    case doneLeft hm hp =>
      cases h
    case yieldRight out₁ hm it₂' out₂ hp =>
      cases h
      apply ZipH.rel₁_of_memoizedLeft
      simp [Option.lt, hm]
    case skipRight out₁ hm it₂' hp =>
      cases h
      apply ZipH.rel₁_of_right
      · simp_all
      · exact hp
    case doneRight out₁ hm hp =>
      cases h

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
def ZipH.rel₂ [Productive α₁ m] [Finite α₂ m] :
    Iter (α := ZipH α₁ m α₂ β₂) m (β₁ × β₂) → Iter (α := ZipH α₁ m α₂ β₂) m (β₁ × β₂) → Prop :=
  InvImage (Prod.Lex
      Iter.TerminationMeasures.Finite.rel
      (Prod.Lex (ZipH.lt_with_top emptyRelation) Iter.TerminationMeasures.Productive.rel))
    (fun it => (it.inner.right.finitelyManySteps, (it.inner.memoizedLeft.inflate, it.inner.left.finitelyManySkips)))

theorem ZipH.rel₂_of_right [Productive α₁ m] [Finite α₂ m] {it' it : Iter (α := ZipH α₁ m α₂ β₂) m (β₁ × β₂)}
    (h : it'.inner.right.finitelyManySteps.rel it.inner.right.finitelyManySteps) : ZipH.rel₂ m it' it :=
  Prod.Lex.left _ _ h

theorem ZipH.rel₂_of_memoizedLeft [Productive α₁ m] [Finite α₂ m]
    {right : Iter (α := α₂) m β₂} {b' b} {left' left : Iter (α := α₁) m β₁}
    (h : lt_with_top emptyRelation b'.inflate b.inflate) :
    ZipH.rel₂ m ⟨left, b', right⟩ ⟨left', b, right⟩ :=
  Prod.Lex.right _ <| Prod.Lex.left _ _ (by simp only [USquash.inflate_deflate]; exact h)

theorem ZipH.rel₂_of_left [Productive α₁ m] [Finite α₂ m]
    {right : Iter (α := α₂) m β₂} {b b' : _} {it' it : Iter (α := α₁) m β₁}
    (h : b.inflate = b'.inflate)
    (h' : it'.finitelyManySkips.rel it.finitelyManySkips) :
    ZipH.rel₂ m ⟨it', b, right⟩ ⟨it, b', right⟩ := by
  cases USquash.inflate.inj h
  exact Prod.Lex.right _ <| Prod.Lex.right _ h'

instance [Monad m] [Productive α₁ m] [Finite α₂ m] :
    FinitenessRelation (ZipH α₁ m α₂ β₂) m where
  rel := ZipH.rel₂ m
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact WellFoundedRelation.wf
    · refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
      · apply ZipH.wellFounded_lt_with_top
        exact emptyWf.wf
      · apply InvImage.wf
        exact Productive.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case yieldLeft hm it' out hp =>
      cases h
      apply ZipH.rel₂_of_memoizedLeft
      simp_all [ZipH.lt_with_top]
    case skipLeft hm it' hp =>
      cases h
      apply ZipH.rel₂_of_left
      · simp_all
      · exact hp
    case doneLeft hm hp =>
      cases h
    case yieldRight out₁ hm it₂' out₂ hp =>
      cases h
      apply ZipH.rel₂_of_right
      apply Iter.plausible_successor_of_yield hp
    case skipRight out₁ hm it₂' hp =>
      cases h
      apply ZipH.rel₂_of_right
      apply Iter.plausible_successor_of_skip hp
    case doneRight out₁ hm hp =>
      cases h

instance ZipH.instIteratorToArray [Monad m] [Finite (ZipH α₁ m α₂ β₂) m] : IteratorToArray (ZipH α₁ m α₂ β₂) m :=
  .defaultImplementation

instance ZipH.instIteratorFor [Monad m] [Monad n] [MonadLiftT m n] [Finite (ZipH α₁ m α₂ β₂) m] :
    IteratorFor (ZipH α₁ m α₂ β₂) m n :=
  .defaultImplementation

end ZipH

-- TODO: Does it make sense to have this specialized version?
section Zip

universe u v

variable {α₁ α₂ : Type w} {β₁ β₂ : Type v} {m : Type w → Type w'}
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
def Iter.zip
    (left : Iter (α := α₁) m β₁) (right : Iter (α := α₂) m β₂) :=
  (Iter.zipH left right : Iter m (β₁ × β₂))

end Zip
