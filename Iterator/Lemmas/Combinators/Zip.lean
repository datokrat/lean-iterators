/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Combinators.Take
import Iterator.Combinators.Zip
import Iterator.Consumers.Access
import Iterator.Lemmas.Monadic.Zip
import Iterator.Lemmas.Combinators.Take
import Iterator.Lemmas.Consumers

def Iter.Intermediate.zip {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁]
    (it₁ : Iter (α := α₁) β₁)
    (memo : (Option { out : β₁ //
        ∃ it : Iter (α := α₁) β₁, it.toIterM.plausible_output out }))
    (it₂ : Iter (α := α₂) β₂) :
    Iter (α := Zip α₁ Id α₂ β₂) (β₁ × β₂) :=
  (IterM.Intermediate.zip
    it₁.toIterM
    ((fun x => ⟨x.1, x.2.choose.toIterM, x.2.choose_spec⟩) <$> memo)
    it₂.toIterM).toPureIter

def Iter.Intermediate.zip_inj {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] :
    ∀ {it₁ it₁' : Iter (α := α₁) β₁} {memo memo'} {it₂ it₂' : Iter (α := α₂) β₂},
      zip it₁ memo it₂ = zip it₁' memo' it₂' ↔ it₁ = it₁' ∧ memo = memo' ∧ it₂ = it₂' := by
  intro it₁ it₁' memo memo' it₂ it₂'
  apply Iff.intro
  · intro h
    cases it₁; cases it₁'; cases it₂; cases it₂'
    obtain _ | ⟨⟨_⟩⟩ := memo <;> obtain _ | ⟨⟨_⟩⟩ := memo' <;>
      simp_all [toIterM, IterM.toPureIter, zip, IterM.Intermediate.zip, Option.map_eq_map]
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

def Iter.Intermediate.zip_surj {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] :
    ∀ it : Iter (α := Zip α₁ Id α₂ β₂) (β₁ × β₂), ∃ it₁ memo it₂, it = Intermediate.zip it₁ memo it₂ := by
  refine fun it => ⟨it.inner.left.toPureIter,
      (fun x => ⟨x.1, x.2.choose.toPureIter, x.2.choose_spec⟩) <$> it.inner.memoizedLeft,
      it.inner.right.toPureIter, ?_⟩
  simp only [zip, toIterM_toPureIter, Option.map_eq_map, Option.map_map]
  change it = (IterM.Intermediate.zip _ (Option.map id it.inner.memoizedLeft) it.inner.right).toPureIter
  simp only [Option.map_id_fun, id_eq]
  rfl

theorem Iter.zip_eq_intermediateZip {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁]
    [Iterator α₂ Id β₂]
    (it₁ : Iter (α := α₁) β₁) (it₂ : Iter (α := α₂) β₂) :
    it₁.zip it₂ = Intermediate.zip it₁ none it₂ := by
  rfl

theorem Iter.step_intermediateZip {α₁ α₂ β₁ β₂}
    [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    {it₁ : Iter (α := α₁) β₁}
    {memo : Option { out : β₁ //
        ∃ it : Iter (α := α₁) β₁, it.toIterM.plausible_output out }}
    {it₂ : Iter (α := α₂) β₂} :
    (Intermediate.zip it₁ memo it₂).step = (
      match memo with
      | none =>
        match it₁.step with
        | .yield it₁' out hp =>
          .skip (Intermediate.zip it₁' (some ⟨out, _, _, hp⟩) it₂)
            (.yieldLeft rfl hp)
        | .skip it₁' hp =>
          .skip (Intermediate.zip it₁' none it₂)
            (.skipLeft rfl hp)
        | .done hp =>
          .done (.doneLeft rfl hp)
      | some out₁ =>
        match it₂.step with
        | .yield it₂' out₂ hp =>
          .yield (Intermediate.zip it₁ none it₂') (out₁, out₂)
            (.yieldRight (it := Intermediate.zip it₁ (some out₁) it₂ |>.toIterM) rfl hp)
        | .skip it₂' hp =>
          .skip (Intermediate.zip it₁ (some out₁) it₂')
            (.skipRight rfl hp)
        | .done hp =>
          .done (.doneRight rfl hp)) := by
  simp only [Intermediate.zip, IterM.step_intermediateZip, Iter.step, toIterM_toPureIter]
  cases memo
  case none =>
    obtain ⟨step, h⟩ := it₁.toIterM.step
    cases step
    · simp [PlausibleIterStep.map, PlausibleIterStep.skip, Id.run]
    · simp [PlausibleIterStep.map, PlausibleIterStep.skip, Id.run]
    · simp [PlausibleIterStep.map, PlausibleIterStep.done, Id.run]
  case some out₁ =>
    obtain ⟨step, h⟩ := it₂.toIterM.step
    cases step
    · simp [PlausibleIterStep.map, PlausibleIterStep.yield, Id.run]
    · simp [PlausibleIterStep.map, PlausibleIterStep.skip, Id.run]
    · simp [PlausibleIterStep.map, PlausibleIterStep.done, Id.run]

/-
* (x.zip y).toList = x.toList.zip y.toList (if x, y finite)
* ((x.take n).zip (y.take n)).toList = ((x.zip y).take n).toList (if x, y productive)
* one-sided variants
-/

theorem Iter.toList_intermediateZip_of_finite {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    {it₁ : Iter (α := α₁) β₁} {memo} {it₂ : Iter (α := α₂) β₂}
    [Finite α₁ Id] [Finite α₂ Id]
    [IteratorToArray α₁ Id] [LawfulIteratorToArray α₁ Id]
    [IteratorToArray α₂ Id] [LawfulIteratorToArray α₂ Id]
    [IteratorToArray (Zip α₁ Id α₂ β₂) Id]
    [LawfulIteratorToArray (Zip α₁ Id α₂ β₂) Id] :
    (Intermediate.zip it₁ memo it₂).toList = ((memo.map Subtype.val).toList ++ it₁.toList).zip it₂.toList := by
  generalize h : Intermediate.zip it₁ memo it₂ = it
  revert h it₁ memo it₂
  induction it using Iter.induct with | step _ ihy ihs
  rintro it₁ memo it₂ rfl
  rw [Iter.toList_of_step]
  match hs : (Intermediate.zip it₁ memo it₂).step with
  | .yield it' out hp =>
    rw [step_intermediateZip] at hs
    cases memo
    case none =>
      generalize it₁.step = step₁ at *
      obtain ⟨step₁, h₁⟩ := step₁
      cases step₁ <;> cases hs
    case some =>
      rw [Iter.toList_of_step (it := it₂)]
      generalize it₂.step = step₂ at *
      obtain ⟨step₂, h₂⟩ := step₂
      cases step₂
      · cases hs
        simp [ihy hp rfl]
      · cases hs
      · cases hs
  | .skip it' hp =>
    rw [step_intermediateZip] at hs
    cases memo
    case none =>
      rw [Iter.toList_of_step (it := it₁)]
      generalize it₁.step = step₁ at *
      obtain ⟨step₁, h₁⟩ := step₁
      cases step₁
      · cases hs
        simp [ihs hp rfl]
      · cases hs
        simp [ihs hp rfl]
      · cases hs
    case some =>
      rw [Iter.toList_of_step (it := it₂)]
      generalize it₂.step = step₂ at *
      obtain ⟨step₂, h₂⟩ := step₂
      cases step₂
      · cases hs
      · cases hs
        simp [ihs hp rfl]
      · cases hs
  | .done hp =>
    rw [step_intermediateZip] at hs
    cases memo
    case none =>
      rw [Iter.toList_of_step (it := it₁)]
      generalize it₁.step = step₁ at *
      obtain ⟨step₁, h₁⟩ := step₁
      cases step₁
      · cases hs
      · cases hs
      · cases hs
        simp
    case some =>
      rw [Iter.toList_of_step (it := it₂)]
      generalize it₂.step = step₂ at *
      obtain ⟨step₂, h₁⟩ := step₂
      cases step₂
      · cases hs
      · cases hs
      · cases hs
        simp

-- TODO: don't require `Productive (Zip ..) Id` explicitly
theorem Iter.getAtIdx?_intermediateZip {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    [Productive α₁ Id] [Productive α₂ Id] [Productive (Zip α₁ Id α₂ β₂) Id]
    {it₁ : Iter (α := α₁) β₁} {memo} {it₂ : Iter (α := α₂) β₂} {n : Nat} :
    (Intermediate.zip it₁ memo it₂).getAtIdx? n =
      (match memo with
      | none => do return (← it₁.getAtIdx? n, ← it₂.getAtIdx? n)
      | some memo => match n with
        | 0 => do return (memo.val, ← it₂.getAtIdx? n)
        | n' + 1 => do return (← it₁.getAtIdx? n', ← it₂.getAtIdx? (n' + 1))) := by
  generalize h : Intermediate.zip it₁ memo it₂ = it
  revert h it₁ memo it₂
  fun_induction it.getAtIdx? n
  rintro it₁ memo it₂ rfl
  case case1 it it' out h h' =>
    rw [getAtIdx?, h']
    simp only [Option.pure_def, Option.bind_eq_bind]
    simp [step_intermediateZip] at h'
    split at h'
    · split at h' <;> cases h'
    · split at h' <;> cases h'
      rename_i hs₂
      rw [getAtIdx?, hs₂]
      simp
  case case2 it it' out h  h' n ih =>
    rintro it₁ memo it₂ rfl
    rw [getAtIdx?, h']
    simp only [Nat.succ_eq_add_one, Option.pure_def, Option.bind_eq_bind]
    cases memo
    case none =>
      rw [step_intermediateZip] at h'
      simp only at h'
      split at h' <;> cases h'
    case some =>
      rw [step_intermediateZip] at h'
      simp only at h'
      split at h' <;> cases h'
      rename_i hs₂
      simp only [ih rfl, Option.pure_def, Option.bind_eq_bind]
      rw [getAtIdx?.eq_def (it := it₂), hs₂]
  case case3 it it' h h' ih =>
    rintro it₁ memo it₂ rfl
    obtain ⟨it₁', memo', it₂', rfl⟩ := Intermediate.zip_surj it'
    specialize ih rfl
    rw [getAtIdx?, h']
    rw [step_intermediateZip] at h'
    simp [PlausibleIterStep.skip] at h'
    rw [Subtype.ext_iff] at h'
    split at h'
    · split at h' <;> rename_i hs₁
      · simp only [IterStep.skip.injEq, Intermediate.zip_inj] at h'
        obtain ⟨rfl, rfl, rfl⟩ := h'
        simp [ih, getAtIdx?.eq_def (it := it₁), hs₁]
        split <;> rfl
      · simp only [IterStep.skip.injEq, Intermediate.zip_inj] at h'
        obtain ⟨rfl, rfl, rfl⟩ := h'
        simp [ih, getAtIdx?.eq_def (it := it₁), hs₁]
      · cases h'
    · split at h' <;> rename_i hs₂ <;> (try cases h')
      simp only [IterStep.skip.injEq, Intermediate.zip_inj] at h'
      obtain ⟨rfl, rfl, rfl⟩ := h'
      simp [ih, getAtIdx?.eq_def (it := it₂), hs₂]
  case case4 it _ h =>
    rintro it₁ memo it₂ rfl
    rw [getAtIdx?, h]
    simp [step_intermediateZip] at h
    cases memo
    case none =>
      simp at h
      split at h <;> cases h
      rename_i hs₁
      simp [getAtIdx?.eq_def (it := it₁), hs₁]
    case some =>
      simp at h
      split at h <;> cases h
      rename_i hs₂
      simp [getAtIdx?.eq_def (it := it₂), hs₂]
      split <;> rfl

-- TODO: don't require `Productive (Zip ..) Id` explicitly
theorem Iter.getAtIdx?_zip {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    [Productive α₁ Id] [Productive α₂ Id] [Productive (Zip α₁ Id α₂ β₂) Id]
    {it₁ : Iter (α := α₁) β₁} {it₂ : Iter (α := α₂) β₂} {n : Nat} :
    (it₁.zip it₂).getAtIdx? n = do return (← it₁.getAtIdx? n, ← it₂.getAtIdx? n) := by
  rw [zip_eq_intermediateZip, getAtIdx?_intermediateZip]

-- TODO: don't require `Productive (Zip ..) Id` explicitly
theorem Iter.toList_take_intermediateZip {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    [Productive α₁ Id] [Productive α₂ Id] [Productive (Zip α₁ Id α₂ β₂) Id]
    {it₁ : Iter (α := α₁) β₁} {it₂ : Iter (α := α₂) β₂} {n : Nat} :
    ((it₁.zip it₂).take n).toList = ((it₁.take n).zip (it₂.take n)).toList := by
  apply toList_eq_of_getAtIdx?_eq
  intro k
  simp only [getAtIdx?_take, getAtIdx?_zip, Option.pure_def, Option.bind_eq_bind]
  split <;> rfl

theorem Iter.toList_zip_of_finite {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    {it₁ : Iter (α := α₁) β₁} {it₂ : Iter (α := α₂) β₂}
    [Finite α₁ Id] [Finite α₂ Id]
    [IteratorToArray α₁ Id] [LawfulIteratorToArray α₁ Id]
    [IteratorToArray α₂ Id] [LawfulIteratorToArray α₂ Id]
    [IteratorToArray (Zip α₁ Id α₂ β₂) Id]
    [LawfulIteratorToArray (Zip α₁ Id α₂ β₂) Id] :
    (it₁.zip it₂).toList = it₁.toList.zip it₂.toList := by
  simp [zip_eq_intermediateZip, Iter.toList_intermediateZip_of_finite]

theorem Iter.toList_zip_of_finite_left {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    {it₁ : Iter (α := α₁) β₁} {it₂ : Iter (α := α₂) β₂}
    [Finite α₁ Id] [Productive α₂ Id] [IteratorToArray α₁ Id] [LawfulIteratorToArray α₁ Id]
    [IteratorToArray (Zip α₁ Id α₂ β₂) Id]
    [LawfulIteratorToArray (Zip α₁ Id α₂ β₂) Id] :
    (it₁.zip it₂).toList = it₁.toList.zip (it₂.take it₁.toList.length).toList := by
  ext
  simp [List.getElem?_zip_eq_some]
  simp [getElem?_toList_eq_getAtIdx?, getAtIdx?_take, getAtIdx?_zip]
  constructor
  · intro h
    simp [Option.bind_eq_some_iff] at h
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := h
    refine ⟨hb₁, ?_, hb₂⟩
    false_or_by_contra
    rw [← getElem?_toList_eq_getAtIdx?] at hb₁
    rename_i h
    simp only [Nat.not_lt, ← List.getElem?_eq_none_iff, hb₁] at h
    cases h
  · rintro ⟨h₁, h₂, h₃⟩
    simp [h₁, h₃]

theorem Iter.toList_zip_of_finite_right {α₁ α₂ β₁ β₂} [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    {it₁ : Iter (α := α₁) β₁} {it₂ : Iter (α := α₂) β₂}
    [Productive α₁ Id] [Finite α₂ Id] [IteratorToArray α₂ Id] [LawfulIteratorToArray α₂ Id]
    [IteratorToArray (Zip α₁ Id α₂ β₂) Id]
    [LawfulIteratorToArray (Zip α₁ Id α₂ β₂) Id] :
    (it₁.zip it₂).toList = (it₁.take it₂.toList.length).toList.zip it₂.toList := by
  ext
  simp [List.getElem?_zip_eq_some]
  simp [getElem?_toList_eq_getAtIdx?, getAtIdx?_take, getAtIdx?_zip]
  constructor
  · intro h
    simp [Option.bind_eq_some_iff] at h
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := h
    refine ⟨⟨?_, hb₁⟩, hb₂⟩
    false_or_by_contra
    rw [← getElem?_toList_eq_getAtIdx?] at hb₂
    rename_i h
    simp only [Nat.not_lt, ← List.getElem?_eq_none_iff, hb₂] at h
    cases h
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    simp [h₂, h₃]
