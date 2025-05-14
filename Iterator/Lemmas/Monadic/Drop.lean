/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Combinators.Monadic.Drop
import Iterator.Lemmas.Monadic.Consumers

theorem IterM.stepH_drop {α m β} [Monad m] [Iterator α m β] {n : Nat}
    {it : IterM (α := α) m β} :
    (it.drop n).stepH = (do
      match (← it.stepH).inflate with
      | .yield it' out h =>
        match n with
        | 0 => pure <| .deflate <| .yield (it'.drop 0) out (.yield h rfl)
        | k + 1 => pure <| .deflate <| .skip (it'.drop k) (.drop h rfl)
      | .skip it' h => pure <| .deflate <| .skip (it'.drop n) (.skip h)
      | .done h => pure <| .deflate <| .done (.done h)) := by
  simp only [drop, stepH, Iterator.step, inner_toIter, Nat.succ_eq_add_one]
  apply bind_congr
  intro step
  obtain ⟨step, h⟩ := step.inflate
  cases step
  · cases n <;> rfl
  · rfl
  · rfl

theorem IterM.step_drop {α m β} [Monad m] [LawfulMonad m] [Iterator α m β] {n : Nat}
    {it : IterM (α := α) m β} :
    (it.drop n).step = (do
      match ← it.step with
      | .yield it' out h =>
        match n with
        | 0 => pure <| .yield (it'.drop 0) out (.yield h rfl)
        | k + 1 => pure <| .skip (it'.drop k) (.drop h rfl)
      | .skip it' h => pure <| .skip (it'.drop n) (.skip h)
      | .done h => pure <| .done (.done h)) := by
  simp only [IterM.step, IterM.stepH_drop, map_bind, bind_map_left]
  apply bind_congr
  intro step
  obtain ⟨step, h⟩ := step.inflate
  cases step
  · cases n <;> simp
  · simp
  · simp
