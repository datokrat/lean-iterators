/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic
import Iterator.Consumers.Monadic.Partial

@[specialize]
def IterM.getAtIdx? {α m β} [Iterator α m β] [Productive α m] [Monad m]
    (n : Nat) (it : IterM (α := α) m β) : m (Option β) := do
  match ← it.step with
  | .yield it' out _ =>
    match n with
    | 0 => return some out
    | k + 1 => it'.getAtIdx? k
  | .skip it' _ => it'.getAtIdx? n
  | .done _ => return none
termination_by (n, it.finitelyManySkips)

@[specialize]
partial def IterM.Partial.getAtIdx? {α m β} [Iterator α m β] [Monad m]
    (n : Nat) (it : IterM.Partial (α := α) m β) : m (Option β) := do
  match ← it.it.step with
  | .yield it' out _ =>
    match n with
    | 0 => return some out
    | k + 1 => (⟨it'⟩ : IterM.Partial (α := α) m β).getAtIdx? k
  | .skip it' _ => (⟨it'⟩ : IterM.Partial (α := α) m β).getAtIdx? n
  | .done _ => return none
