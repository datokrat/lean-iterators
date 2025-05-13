/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Consumers
import Iterator.Combinators.Monadic.FilterMap
import Iterator.Lemmas.Monadic.Equivalence
import Iterator.Producers

section Consumers

def IterM.induct {α m β} [Iterator α m β] [Finite α m]
  (motive : IterM (α := α) m β → Sort x)
  (step : (it : IterM (α := α) m β) →
    (ih_yield : ∀ {it' : IterM (α := α) m β} {out : β}, it.plausible_step (.yield it' out) → motive it') →
    (ih_skip : ∀ {it' : IterM (α := α) m β}, it.plausible_step (.skip it') → motive it' ) →
    motive it) (it : IterM (α := α) m β) : motive it :=
  step _ (fun {it' _} _ => IterM.induct motive step it') (fun {it'} _ => IterM.induct motive step it')
termination_by it.finitelyManySteps

theorem IterM.DefaultConsumers.toArrayMapped.go.aux₁ [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} {b : γ} {bs : Array γ} {f : β → m γ} :
    IterM.DefaultConsumers.toArrayMapped.go f it (#[b] ++ bs) = (#[b] ++ ·) <$> IterM.DefaultConsumers.toArrayMapped.go f it bs := by
  induction it, bs using IterM.DefaultConsumers.toArrayMapped.go.induct
  next it bs ih₁ ih₂ =>
  rw [go, map_eq_pure_bind, go, bind_assoc]
  refine congrArg (IterM.stepH it >>= ·) ?_
  ext step
  generalize step.inflate = step
  split
  · simp [ih₁ _ _ ‹_›]
  · simp [ih₂ _ ‹_›]
  · simp

theorem IterM.DefaultConsumers.toArrayMapped.go.aux₂ [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] {it : IterM (α := α) m β} {acc : Array γ} {f : β → m γ} :
    IterM.DefaultConsumers.toArrayMapped.go f it acc =
      (acc ++ ·) <$> IterM.DefaultConsumers.toArrayMapped f it := by
  rw [← Array.toArray_toList (xs := acc)]
  generalize acc.toList = acc
  induction acc with
  | nil => simp [toArrayMapped]
  | cons x xs ih =>
    rw [List.toArray_cons, IterM.DefaultConsumers.toArrayMapped.go.aux₁, ih]
    simp only [Functor.map_map, Array.append_assoc]

theorem IterM.DefaultConsumers.toArrayMapped_of_stepH [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] {it : IterM (α := α) m β} {f : β → m γ} :
    IterM.DefaultConsumers.toArrayMapped f it = (do
      match (← it.stepH).inflate with
      | .yield it' out _ => return #[← f out] ++ (← IterM.DefaultConsumers.toArrayMapped f it')
      | .skip it' _ => IterM.DefaultConsumers.toArrayMapped f it'
      | .done _ => return #[]) := by
  rw [IterM.DefaultConsumers.toArrayMapped, IterM.DefaultConsumers.toArrayMapped.go]
  apply bind_congr
  intro step
  generalize step.inflate = step
  split <;> simp [IterM.DefaultConsumers.toArrayMapped.go.aux₂]

theorem IterM.DefaultConsumers.toArrayMapped_of_step [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] {it : IterM (α := α) m β} {f : β → m γ} :
    IterM.DefaultConsumers.toArrayMapped f it = (do
      match ← it.step with
      | .yield it' out _ => return #[← f out] ++ (← IterM.DefaultConsumers.toArrayMapped f it')
      | .skip it' _ => IterM.DefaultConsumers.toArrayMapped f it'
      | .done _ => return #[]) := by
  rw [IterM.DefaultConsumers.toArrayMapped_of_stepH, IterM.step, map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro step
  generalize step.inflate = step
  rw [pure_bind]
  rfl

theorem IterM.toArray_of_step [Monad m] [LawfulMonad m]
    [Iterator α m β] [IteratorToArray α m] [LawfulIteratorToArray α m]
    {it : IterM (α := α) m β} :
    it.toArray = (do
      match ← it.step with
      | .yield it' out _ => return #[out] ++ (← it'.toArray)
      | .skip it' _ => it'.toArray
      | .done _ => return #[]) := by
  rw [IterM.toArray, LawfulIteratorToArray.lawful, IterM.DefaultConsumers.toArrayMapped_of_step]
  simp only [bind_pure_comp, pure_bind, toArray, LawfulIteratorToArray.lawful]

theorem IterM.toList_toArray [Monad m] [Iterator α m β] [IteratorToArray α m]
    {it : IterM (α := α) m β} :
    Array.toList <$> it.toArray = it.toList := by
  simp [IterM.toList]

theorem IterM.toArray_toList [Monad m] [LawfulMonad m] [Iterator α m β] [IteratorToArray α m]
    {it : IterM (α := α) m β} :
    List.toArray <$> it.toList = it.toArray := by
  simp [IterM.toList]

theorem IterM.toList_of_step [Monad m] [LawfulMonad m] [Iterator α m β]
    [IteratorToArray α m] [LawfulIteratorToArray α m] {it : IterM (α := α) m β} :
    it.toList = (do
      match ← it.step with
      | .yield it' out _ => return out :: (← it'.toList)
      | .skip it' _ => it'.toList
      | .done _ => return []) := by
  simp [← IterM.toList_toArray]
  rw [IterM.toArray_of_step, map_eq_pure_bind, bind_assoc]
  refine congrArg (_ >>= ·) ?_
  ext step
  split <;> simp

theorem IterM.toListRev.go.aux₁ [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} {b : β} {bs : List β} :
    IterM.toListRev.go it (bs ++ [b]) = (· ++ [b]) <$> IterM.toListRev.go it bs:= by
  induction it, bs using IterM.toListRev.go.induct
  next it bs ih₁ ih₂ =>
  rw [go, go, map_eq_pure_bind, bind_assoc]
  refine congrArg (IterM.step it >>= ·) ?_
  ext step
  simp only [List.cons_append] at ih₁
  split <;> simp [*]

theorem IterM.toListRev.go.aux₂ [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} {acc : List β} :
    IterM.toListRev.go it acc = (· ++ acc) <$> it.toListRev := by
  rw [← List.reverse_reverse (as := acc)]
  generalize acc.reverse = acc
  induction acc with
  | nil => simp [toListRev]
  | cons x xs ih => simp [IterM.toListRev.go.aux₁, ih]

theorem IterM.toListRev_of_step [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} :
    it.toListRev = (do
      match ← it.step with
      | .yield it' out _ => return (← it'.toListRev) ++ [out]
      | .skip it' _ => it'.toListRev
      | .done _ => return []) := by
  simp [IterM.toListRev]
  rw [toListRev.go]
  refine congrArg (it.step >>= ·) ?_
  ext step
  obtain ⟨step, h⟩ := step
  cases step <;> simp [IterM.toListRev.go.aux₂]

-- TODO: rename `toListRev` -> `toListRev`
theorem IterM.reverse_toListRev [Monad m] [LawfulMonad m] [Iterator α m β]
    [IteratorToArray α m] [LawfulIteratorToArray α m]
    {it : IterM (α := α) m β} :
    List.reverse <$> it.toListRev = it.toList := by
  apply Eq.symm
  induction it using IterM.induct
  rename_i it ihy ihs
  rw [toListRev_of_step, toList_of_step, map_eq_pure_bind, bind_assoc]
  refine congrArg (_ >>= ·) ?_
  ext step
  split <;> simp (discharger := assumption) [ihy, ihs]

end Consumers

section Congruence

theorem IterM.Morphism.toArrayMapped_eq {α α' : Type w} {m : Type w → Type w'}
    {β : Type v} {γ : Type w}
    [Monad m] [LawfulMonad m]
    [Iterator α m β] [Iterator α' m β] [IteratorToArray α m] [LawfulIteratorToArray α m]
    [IteratorToArray α' m] [LawfulIteratorToArray α' m]
    (φ : Morphism α α' m) {f : β → m γ} {it : IterM (α := α) m β} :
    IteratorToArray.toArrayMapped f it = IteratorToArray.toArrayMapped f (φ.map it) := by
  haveI : Finite α m := LawfulIteratorToArray.finite
  haveI : Finite α' m := LawfulIteratorToArray.finite
  simp only [LawfulIteratorToArray.lawful]
  induction it using IterM.induct with | step it ihy ihs =>
  rw [DefaultConsumers.toArrayMapped_of_stepH, DefaultConsumers.toArrayMapped_of_stepH]
  simp only [← φ.stepH_hom, map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro step
  generalize step.inflate = step
  obtain ⟨step, _⟩ := step
  cases step <;> simp (discharger := assumption) [PlausibilityMorphism.mapStep, IterStep.map, ihs, ihy]

theorem IterM.Morphism.toArray_eq {α α' : Type w} {m : Type w → Type w'} {β : Type w}
    [Monad m] [LawfulMonad m]
    [Iterator α m β] [Iterator α' m β] [IteratorToArray α m] [LawfulIteratorToArray α m]
    [IteratorToArray α' m] [LawfulIteratorToArray α' m]
    (φ : Morphism α α' m) {it : IterM (α := α) m β} :
    it.toArray = (φ.map it).toArray := by
  simp [IterM.toArray, φ.toArrayMapped_eq]

theorem IterM.Morphism.toList_eq {α α' : Type w} {m : Type w → Type w'} {β : Type w}
    [Monad m] [LawfulMonad m]
    [Iterator α m β] [Iterator α' m β] [IteratorToArray α m] [LawfulIteratorToArray α m]
    [IteratorToArray α' m] [LawfulIteratorToArray α' m]
    (φ : Morphism α α' m) {it : IterM (α := α) m β} :
    it.toList = (φ.map it).toList := by
  simp [← IterM.toList_toArray, φ.toArray_eq]

end Congruence
