/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Pure

structure Iter.Partial {α : Type w} (β : Type v) where
  it : Iter (α := α) β

@[always_inline, inline]
def Iter.allowNontermination {α : Type w} {β : Type w}
    (it : Iter (α := α) β) : Iter.Partial (α := α) β :=
  ⟨it⟩
