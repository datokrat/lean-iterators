/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic
import Iterator.Consumers.Collect
import Iterator.Consumers.Loop

section Zip

universe u₁ u₂ w

variable {m : Type w → Type w'}
  {α₁ : Type w} {β₁ : Type w} [Iterator α₁ m β₁]
  {α₂ : Type w} {β₂ : Type w} [Iterator α₂ m β₂]

structure Zip (α₁ : Type w) (m : Type w → Type w') {β₁ : Type w} [Iterator α₁ m β₁] (α₂ : Type w) (β₂ : Type w) where
  left : IterM (α := α₁) m β₁
  memoizedLeft : (Option { out : β₁ // ∃ it : IterM (α := α₁) m β₁, it.plausible_output out })
  right : IterM (α := α₂) m β₂

inductive Zip.PlausibleStep (it : IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂)) :
    IterStep (IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂)) (β₁ × β₂) → Prop where
  | yieldLeft (hm : it.inner.memoizedLeft = none) {it' out} (hp : it.inner.left.plausible_step (.yield it' out)) :
      PlausibleStep it (.skip ⟨⟨it', (some ⟨out, _, _, hp⟩), it.inner.right⟩⟩)
  | skipLeft (hm : it.inner.memoizedLeft = none) {it'} (hp : it.inner.left.plausible_step (.skip it')) :
      PlausibleStep it (.skip ⟨⟨it', none, it.inner.right⟩⟩)
  | doneLeft (hm : it.inner.memoizedLeft = none) (hp : it.inner.left.plausible_step .done) :
      PlausibleStep it .done
  | yieldRight {out₁} (hm : it.inner.memoizedLeft = some out₁) {it₂' out₂} (hp : it.inner.right.plausible_step (.yield it₂' out₂)) :
      PlausibleStep it (.yield ⟨⟨it.inner.left, none, it₂'⟩⟩ (out₁, out₂))
  | skipRight {out₁} (hm : it.inner.memoizedLeft = some out₁) {it₂'} (hp : it.inner.right.plausible_step (.skip it₂')) :
      PlausibleStep it (.skip ⟨⟨it.inner.left, (some out₁), it₂'⟩⟩)
  | doneRight {out₁} (hm : it.inner.memoizedLeft = some out₁) (hp : it.inner.right.plausible_step .done) :
      PlausibleStep it .done

instance Zip.instIterator [Monad m] :
    Iterator (Zip α₁ m α₂ β₂) m (β₁ × β₂) where
  plausible_step := PlausibleStep
  step it :=
    match hm : it.inner.memoizedLeft with
    | none => do
      match ← it.inner.left.step with
      | .yield it₁' out hp =>
          pure <| .skip ⟨⟨it₁', (some ⟨out, _, _, hp⟩), it.inner.right⟩⟩ (.yieldLeft hm hp)
      | .skip it₁' hp =>
          pure <| .skip ⟨⟨it₁', none, it.inner.right⟩⟩ (.skipLeft hm hp)
      | .done hp =>
          pure <| .done (.doneLeft hm hp)
    | some out₁ => do
      match ← it.inner.right.step with
      | .yield it₂' out₂ hp =>
          pure <| .yield ⟨⟨it.inner.left, none, it₂'⟩⟩ (out₁, out₂) (.yieldRight hm hp)
      | .skip it₂' hp =>
          pure <| .skip ⟨⟨it.inner.left, (some out₁), it₂'⟩⟩ (.skipRight hm hp)
      | .done hp =>
          pure <| .done (.doneRight hm hp)

@[inline]
def IterM.zip [Monad m]
    (left : IterM (α := α₁) m β₁) (right : IterM (α := α₂) m β₂) :
    IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) :=
  toIter ⟨left, none, right⟩ m _

-- TODO: put this into core. This is also duplicated in FlatMap
theorem Zip.wellFounded_optionLt {α} {rel : α → α → Prop} (h : WellFounded rel) :
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
def Zip.rel₁ [Finite α₁ m] [Productive α₂ m] :
    IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) → IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) → Prop :=
  InvImage (Prod.Lex
      IterM.TerminationMeasures.Finite.rel
      (Prod.Lex (Option.lt emptyRelation) IterM.TerminationMeasures.Productive.rel))
    (fun it => (it.inner.left.finitelyManySteps, (it.inner.memoizedLeft, it.inner.right.finitelyManySkips)))

theorem Zip.rel₁_of_left [Finite α₁ m] [Productive α₂ m] {it' it : IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂)}
    (h : it'.inner.left.finitelyManySteps.rel it.inner.left.finitelyManySteps) : Zip.rel₁ m it' it :=
  Prod.Lex.left _ _ h

theorem Zip.rel₁_of_memoizedLeft [Finite α₁ m] [Productive α₂ m]
    {left : IterM (α := α₁) m β₁} {b' b} {right' right : IterM (α := α₂) m β₂}
    (h : Option.lt emptyRelation b' b) :
    Zip.rel₁ m ⟨left, b', right'⟩ ⟨left, b, right⟩ :=
  Prod.Lex.right _ <| Prod.Lex.left _ _ h

theorem Zip.rel₁_of_right [Finite α₁ m] [Productive α₂ m]
    {left : IterM (α := α₁) m β₁} {b b' : _} {it' it : IterM (α := α₂) m β₂}
    (h : b' = b)
    (h' : it'.finitelyManySkips.rel it.finitelyManySkips) :
    Zip.rel₁ m ⟨left, b', it'⟩ ⟨left, b, it⟩ := by
  cases h
  exact Prod.Lex.right _ <| Prod.Lex.right _ h'

instance [Monad m] [Finite α₁ m] [Productive α₂ m] :
    FinitenessRelation (Zip α₁ m α₂ β₂) m where
  rel := Zip.rel₁ m
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact WellFoundedRelation.wf
    · refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
      · apply Zip.wellFounded_optionLt
        exact emptyWf.wf
      · exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case yieldLeft hm it' out hp =>
      cases h
      apply Zip.rel₁_of_left
      exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
    case skipLeft hm it' hp =>
      cases h
      apply Zip.rel₁_of_left
      exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
    case doneLeft hm hp =>
      cases h
    case yieldRight out₁ hm it₂' out₂ hp =>
      cases h
      apply Zip.rel₁_of_memoizedLeft
      simp [Option.lt, hm]
    case skipRight out₁ hm it₂' hp =>
      cases h
      apply Zip.rel₁_of_right
      · simp_all
      · exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›
    case doneRight out₁ hm hp =>
      cases h

def Zip.lt_with_top {α} (r : α → α → Prop) : Option α → Option α → Prop
  | none, _ => false
  | some _, none => true
  | some a', some a => r a' a

theorem Zip.wellFounded_lt_with_top {α} {r : α → α → Prop} (h : WellFounded r) :
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
def Zip.rel₂ [Productive α₁ m] [Finite α₂ m] :
    IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) → IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) → Prop :=
  InvImage (Prod.Lex
      IterM.TerminationMeasures.Finite.rel
      (Prod.Lex (Zip.lt_with_top emptyRelation) IterM.TerminationMeasures.Productive.rel))
    (fun it => (it.inner.right.finitelyManySteps, (it.inner.memoizedLeft, it.inner.left.finitelyManySkips)))

theorem Zip.rel₂_of_right [Productive α₁ m] [Finite α₂ m] {it' it : IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂)}
    (h : it'.inner.right.finitelyManySteps.rel it.inner.right.finitelyManySteps) : Zip.rel₂ m it' it :=
  Prod.Lex.left _ _ h

theorem Zip.rel₂_of_memoizedLeft [Productive α₁ m] [Finite α₂ m]
    {right : IterM (α := α₂) m β₂} {b' b} {left' left : IterM (α := α₁) m β₁}
    (h : lt_with_top emptyRelation b' b) :
    Zip.rel₂ m ⟨left, b', right⟩ ⟨left', b, right⟩ :=
  Prod.Lex.right _ <| Prod.Lex.left _ _ h

theorem Zip.rel₂_of_left [Productive α₁ m] [Finite α₂ m]
    {right : IterM (α := α₂) m β₂} {b b' : _} {it' it : IterM (α := α₁) m β₁}
    (h : b' = b)
    (h' : it'.finitelyManySkips.rel it.finitelyManySkips) :
    Zip.rel₂ m ⟨it', b', right⟩ ⟨it, b, right⟩ := by
  cases h
  exact Prod.Lex.right _ <| Prod.Lex.right _ h'

instance [Monad m] [Productive α₁ m] [Finite α₂ m] :
    FinitenessRelation (Zip α₁ m α₂ β₂) m where
  rel := Zip.rel₂ m
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact WellFoundedRelation.wf
    · refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
      · apply Zip.wellFounded_lt_with_top
        exact emptyWf.wf
      · exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case yieldLeft hm it' out hp =>
      cases h
      apply Zip.rel₂_of_memoizedLeft
      simp_all [Zip.lt_with_top]
    case skipLeft hm it' hp =>
      cases h
      apply Zip.rel₂_of_left
      · simp_all
      · exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›
    case doneLeft hm hp =>
      cases h
    case yieldRight out₁ hm it₂' out₂ hp =>
      cases h
      apply Zip.rel₂_of_right
      exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
    case skipRight out₁ hm it₂' hp =>
      cases h
      apply Zip.rel₂_of_right
      exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
    case doneRight out₁ hm hp =>
      cases h

instance Zip.instIteratorToArray [Monad m] [Finite (Zip α₁ m α₂ β₂) m] : IteratorToArray (Zip α₁ m α₂ β₂) m :=
  .defaultImplementation

instance Zip.instIteratorToArrayPartial [Monad m] : IteratorToArrayPartial (Zip α₁ m α₂ β₂) m :=
  .defaultImplementation

instance Zip.instIteratorFor [Monad m] [Monad n] :
    IteratorFor (Zip α₁ m α₂ β₂) m n :=
  .defaultImplementation

instance Zip.instIteratorForPartial [Monad m] [Monad n] :
    IteratorForPartial (Zip α₁ m α₂ β₂) m n :=
  .defaultImplementation

end Zip
