/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Combinators.Monadic.Take
import Iterator.Lemmas.Monadic.Consumers

theorem IterM.stepH_take {α m β} [Monad m] [Iterator α m β] {n : Nat}
    {it : IterM (α := α) m β} :
    (it.take n).stepH = (match n with
      | 0 => pure <| .deflate <| .done (.depleted rfl)
      | k + 1 => do
        match (← it.stepH).inflate with
        | .yield it' out h => pure <| .deflate <| .yield (it'.take k) out (.yield h rfl)
        | .skip it' h => pure <| .deflate <| .skip (it'.take (k + 1)) (.skip h rfl)
        | .done h => pure <| .deflate <| .done (.done h)) := by
  simp only [take, stepH, Iterator.step, inner_toIter, Nat.succ_eq_add_one]
  cases n
  case zero => rfl
  case succ k =>
    apply bind_congr
    intro step
    generalize step.inflate = step
    obtain ⟨step, h⟩ := step
    cases step <;> rfl

theorem IterM.step_take {α m β} [Monad m] [LawfulMonad m] [Iterator α m β] {n : Nat}
    {it : IterM (α := α) m β} :
    (it.take n).step = (match n with
      | 0 => pure <| .done (.depleted rfl)
      | k + 1 => do
        match ← it.step with
        | .yield it' out h => pure <| .yield (it'.take k) out (.yield h rfl)
        | .skip it' h => pure <| .skip (it'.take (k + 1)) (.skip h rfl)
        | .done h => pure <| .done (.done h)) := by
  simp only [IterM.step, IterM.stepH_take]
  cases n
  case zero => simp
  case succ k =>
    simp only [map_bind, bind_map_left]
    apply bind_congr
    intro step
    generalize step.inflate = step
    obtain ⟨step, h⟩ := step
    cases step <;> simp
