/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Combinators.Monadic.Zip
import Iterator.Lemmas.Monadic.Consumers

def IterM.Intermediate.zipH {α₁ α₂ m β₁ β₂} [Iterator α₁ m β₁]
    (it₁ : IterM (α := α₁) m β₁)
    (memo : (Option { out : β₁ //
        ∃ it : IterM (α := α₁) m β₁, it.plausible_output out }))
    (it₂ : IterM (α := α₂) m β₂) :
    IterM (α := ZipH α₁ m α₂ β₂) m (β₁ × β₂) :=
  ⟨it₁, .deflate memo, it₂⟩

theorem IterM.stepH_intermediateZipH {α₁ α₂ m β₁ β₂} [Monad m]
    [Iterator α₁ m β₁] [Iterator α₂ m β₂]
    {it₁ : IterM (α := α₁) m β₁}
    {memo : Option { out : β₁ //
        ∃ it : IterM (α := α₁) m β₁, it.plausible_output out }}
    {it₂ : IterM (α := α₂) m β₂} :
    (Intermediate.zipH it₁ memo it₂).stepH = (do
      match memo with
      | none =>
        match (← it₁.stepH).inflate with
        | .yield it₁' out hp =>
          pure <| .deflate <| .skip (Intermediate.zipH it₁' (some ⟨out, _, _, hp⟩) it₂)
            (.yieldLeft USquash.inflate_deflate hp)
        | .skip it₁' hp =>
          pure <| .deflate <| .skip (Intermediate.zipH it₁' none it₂)
            (.skipLeft USquash.inflate_deflate hp)
        | .done hp =>
          pure <| .deflate <| .done (.doneLeft USquash.inflate_deflate hp)
      | some out₁ =>
        match (← it₂.stepH).inflate with
        | .yield it₂' out₂ hp =>
          pure <| .deflate <| .yield (Intermediate.zipH it₁ none it₂') (out₁, out₂)
            (.yieldRight USquash.inflate_deflate hp)
        | .skip it₂' hp =>
          pure <| .deflate <| .skip (Intermediate.zipH it₁ (some out₁) it₂')
            (.skipRight USquash.inflate_deflate hp)
        | .done hp =>
          pure <| .deflate <| .done (.doneRight USquash.inflate_deflate hp)) := by
  simp only [Intermediate.zipH, stepH, Iterator.step, inner_toIter]
  split
  · split
    · apply bind_congr
      intro step
      obtain ⟨step, h⟩ := step.inflate
      cases step <;> rfl
    · exfalso; simp_all
  · split
    · exfalso; simp_all
    · rename_i heq
      simp only [USquash.inflate_deflate, Option.some.injEq] at heq
      cases heq
      apply bind_congr
      intro step
      obtain ⟨step, h⟩ := step.inflate
      cases step <;> rfl

theorem IterM.step_intermediateZipH {α₁ α₂ m β₁ β₂} [Monad m] [LawfulMonad m]
    [Iterator α₁ m β₁] [Iterator α₂ m β₂]
    {it₁ : IterM (α := α₁) m β₁}
    {memo : Option { out : β₁ //
        ∃ it : IterM (α := α₁) m β₁, it.plausible_output out }}
    {it₂ : IterM (α := α₂) m β₂} :
    (Intermediate.zipH it₁ memo it₂).step = (do
      match memo with
      | none =>
        match ← it₁.step with
        | .yield it₁' out hp =>
          pure <| .skip (Intermediate.zipH it₁' (some ⟨out, _, _, hp⟩) it₂)
            (.yieldLeft USquash.inflate_deflate hp)
        | .skip it₁' hp =>
          pure <| .skip (Intermediate.zipH it₁' none it₂)
            (.skipLeft USquash.inflate_deflate hp)
        | .done hp =>
          pure <| .done (.doneLeft USquash.inflate_deflate hp)
      | some out₁ =>
        match ← it₂.step with
        | .yield it₂' out₂ hp =>
          pure <| .yield (Intermediate.zipH it₁ none it₂') (out₁, out₂)
            (.yieldRight USquash.inflate_deflate hp)
        | .skip it₂' hp =>
          pure <| .skip (Intermediate.zipH it₁ (some out₁) it₂')
            (.skipRight USquash.inflate_deflate hp)
        | .done hp =>
          pure <| .done (.doneRight USquash.inflate_deflate hp)) := by
  simp only [step, stepH_intermediateZipH]
  cases memo
  · simp only [map_eq_pure_bind, bind_assoc, pure_bind]
    apply bind_congr
    intro step
    obtain ⟨step, h⟩ := step.inflate
    cases step <;> simp
  · simp only [map_eq_pure_bind, bind_assoc, pure_bind]
    apply bind_congr
    intro step
    obtain ⟨step, h⟩ := step.inflate
    cases step
    · simp
    · simp
    · simp
