/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Core

class UnivLE.{u, v} where
  Lift : Type u → Type v
  up : ∀ {α}, α → Lift α
  down : ∀ {α}, Lift α → α
  up_down : ∀ {α : Type u} {a : Lift α}, up (down a) = a
  down_up : ∀ {α : Type u} {a : α}, down (up a) = a

instance UnivLE.max : UnivLE.{u, max u v} where
  Lift α := ULift α
  up a := ULift.up a
  down a := ULift.down a
  up_down := rfl
  down_up := rfl

class IntoUniv.{v} (α : Type u) where
  Into : Type v
  into : α → Shrink
  back : Shrink → α

structure Equiv (α β) where
  hom : α → β
  inv : β → α
  hom_inv : ∀ {b}, hom (inv b) = b
  inv_hom : ∀ {a}, inv (hom a) = a

def Equiv.id {α} : Equiv α α :=
  { hom := _root_.id, inv := _root_.id, hom_inv := rfl, inv_hom := rfl }
