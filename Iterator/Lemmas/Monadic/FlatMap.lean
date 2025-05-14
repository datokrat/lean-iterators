/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Combinators.Monadic.FlatMap
import Iterator.Lemmas.Monadic.Consumers

theorem IterM.flatMapAfter_stepH {α α₂ : Type w} {m : Type w → Type w'} {β : Type w}
    {γ : Type w} [Monad m] [Iterator α m β] [Iterator α₂ m γ]
    {f : β → IterM (α := α₂) m γ} {it₁ : IterM (α := α) m β} {it₂ : Option (IterM (α := α₂) m γ)} :
    (it₁.flatMapAfter f it₂).step = (match it₂ with
    | none => do
        match ← it₁.step with
        | .yield it' innerIt h =>
          pure <| .skip (it'.flatMapAfter f (some <| f innerIt)) (.outerYield h)
        | .skip it' h =>
          pure <| .skip (it'.flatMapAfter f none) (.outerSkip h)
        | .done h =>
          pure <| .done (.outerDone h)
    | some it₂ => do
        match ← it₂.step with
        | .yield it' out h =>
          pure <| .yield (it₁.flatMapAfter f (some it')) out (.innerYield h)
        | .skip it' h =>
          pure <| .skip (it₁.flatMapAfter f (some it')) (.innerSkip h)
        | .done h =>
          pure <| .skip (it₁.flatMapAfter f none) (.innerDone h)) := by
  split
  all_goals
    apply bind_congr
    intro step
    obtain ⟨_ | _ | _, h⟩ := step
    all_goals rfl

theorem IterM.flatMapAfter_step {α α₂ : Type w} {m : Type w → Type w'} {β : Type w}
    {γ : Type w} [Monad m] [LawfulMonad m] [Iterator α m β] [Iterator α₂ m γ]
    {f : β → IterM (α := α₂) m γ} {it₁ : IterM (α := α) m β} {it₂ : Option (IterM (α := α₂) m γ)} :
    (it₁.flatMapAfter f it₂).step = (match it₂ with
    | none => do
        match ← it₁.step with
        | .yield it' innerIt h =>
          pure <| .skip (it'.flatMapAfter f (some <| f innerIt)) (.outerYield h)
        | .skip it' h =>
          pure <| .skip (it'.flatMapAfter f none) (.outerSkip h)
        | .done h =>
          pure <| .done (.outerDone h)
    | some it₂ => do
        match ← it₂.step with
        | .yield it' out h =>
          pure <| .yield (it₁.flatMapAfter f (some it')) out (.innerYield h)
        | .skip it' h =>
          pure <| .skip (it₁.flatMapAfter f (some it')) (.innerSkip h)
        | .done h =>
          pure <| .skip (it₁.flatMapAfter f none) (.innerDone h)) := by
  split
  all_goals
    simp only [IterM.step, flatMapAfter_stepH, map_eq_pure_bind, bind_assoc]
    apply bind_congr
    intro step
    obtain ⟨_ | _ | _, h⟩ := step
    all_goals simp only <;> rfl

theorem IterM.flatMap_stepH {α α₂ : Type w} {m : Type w → Type w'} {β : Type w}
    {γ : Type w} [Monad m] [Iterator α m β] [Iterator α₂ m γ]
    {f : β → IterM (α := α₂) m γ} {it : IterM (α := α) m β} :
    (it.flatMap f).step = (do
      match ← it.step with
      | .yield it' innerIt h =>
        pure <| .skip (it'.flatMapAfter f (some <| f innerIt)) (.outerYield h)
      | .skip it' h =>
        pure <| .skip (it'.flatMap f) (.outerSkip h)
      | .done h =>
        pure <| .done (.outerDone h)) := by
  apply bind_congr
  intro step
  obtain ⟨_ | _ | _, h⟩ := step
  all_goals rfl

theorem IterM.flatMap_step {α α₂ : Type w} {m : Type w → Type w'} {β : Type w}
    {γ : Type w} [Monad m] [LawfulMonad m] [Iterator α m β] [Iterator α₂ m γ]
    {f : β → IterM (α := α₂) m γ} {it : IterM (α := α) m β} :
    (it.flatMap f).step = (do
      match ← it.step with
      | .yield it' innerIt h =>
        pure <| .skip (it'.flatMapAfter f (some <| f innerIt)) (.outerYield h)
      | .skip it' h =>
        pure <| .skip (it'.flatMap f) (.outerSkip h)
      | .done h =>
        pure <| .done (.outerDone h)) := by
  simp only [IterM.step, flatMap_stepH, map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro step
  obtain ⟨(_ | _ | _), h⟩ := step
  all_goals simp only <;> rfl

theorem IterM.toList_flatMapAfter_some {α α₂ : Type w} {m : Type w → Type w'} {β : Type w}
    {γ : Type w} [Monad m] [LawfulMonad m] [Iterator α m β] [Iterator α₂ m γ]
    [Finite α m] [Finite α₂ m]
    [IteratorToArray α m] [IteratorToArray α₂ m]
    [LawfulIteratorToArray α m] [LawfulIteratorToArray α₂ m]
    {f : β → IterM (α := α₂) m γ} {it₂ : IterM (α := α₂) m γ} {it₁ : IterM (α := α) m β} :
    (it₁.flatMapAfter f (some it₂)).toList = (do
      let l ← it₂.toList
      let l' ← (it₁.flatMap f).toList
      return l ++ l') := by
  induction it₂ using IterM.induct with | step it₂ ihy ihs =>
  rw [IterM.toList_of_step, flatMapAfter_step, IterM.toList_of_step]
  simp only [bind_assoc]
  apply bind_congr
  intro step
  match step with
  | .yield it₂' out h =>
    simp only [bind_pure_comp, pure_bind, bind_map_left, List.cons_append_fun]
    simp only [ihy h, map_eq_pure_bind, bind_assoc, pure_bind]
  | .skip it₂' h =>
    simp [ihs h]
  | .done h =>
    simp only [bind_pure_comp, pure_bind, List.nil_append_fun, id_map]
    rfl

theorem IterM.toList_flatMap_of_stepH {α α₂ : Type w} {m : Type w → Type w'} {β : Type w}
    {γ : Type w} [Monad m] [LawfulMonad m] [Iterator α m β] [Iterator α₂ m γ]
    [Finite α m] [Finite α₂ m]
    [IteratorToArray α m] [IteratorToArray α₂ m]
    [LawfulIteratorToArray α m] [LawfulIteratorToArray α₂ m]
    {f : β → IterM (α := α₂) m γ} {it : IterM (α := α) m β} :
    (it.flatMap f).toList = (do
      match ← it.step with
      | .yield it' b _ => do
        let l ← (f b).toList
        let l' ← (it'.flatMap f).toList
        return l ++ l'
      | .skip it' _ =>
        (it'.flatMap f).toList
      | .done _ =>
        pure []) := by
  rw [IterM.toList_of_step, flatMap_step]
  simp only [bind_assoc]
  apply bind_congr
  intro step
  match step with
  | .yield it' out h =>
    simp [toList_flatMapAfter_some]
  | .skip it' h =>
    simp [toList_flatMapAfter_some]
  | .done h =>
    simp

theorem IterM.toList_flatMap_of_pure {α α₂ : Type w} {β : Type w}
    {γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    [Finite α Id] [Finite α₂ Id]
    [IteratorToArray α Id] [IteratorToArray α₂ Id]
    [LawfulIteratorToArray α Id] [LawfulIteratorToArray α₂ Id]
    {f : β → IterM (α := α₂) Id γ} {it : IterM (α := α) Id β} :
    (it.flatMap f).toList = it.toList.flatMap (fun b => (f b).toList) := by
  induction it using IterM.induct with | step it ihy ihs =>
  rw [toList_flatMap_of_stepH, IterM.toList_of_step]
  simp only [Id.pure_eq, Id.bind_eq, Id.map_eq]
  generalize it.step = step
  match step with
  | .yield it' out h =>
    simp [ihy h]
  | .skip it' h =>
    simp [ihs h]
  | .done h =>
    simp
