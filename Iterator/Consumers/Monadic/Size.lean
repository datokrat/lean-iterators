/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic

class IteratorSized (α : Type u) (m : Type w → Type w') where
  size : α → Option Nat
