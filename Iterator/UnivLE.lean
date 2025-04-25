/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Core
import Init.SimpLemmas

class ComputableUnivLE.{u, v} where
  Lift : Type u → Type v
  up : ∀ {α}, α → Lift α
  down : ∀ {α}, Lift α → α
  up_down : ∀ {α : Type u} {a : Lift α}, up (down a) = a
  down_up : ∀ {α : Type u} {a : α}, down (up a) = a

instance ComputableUnivLE.self : ComputableUnivLE.{u, u} where
  Lift α := α
  up := id
  down := id
  up_down := rfl
  down_up := rfl

instance ComputableUnivLE.ofMax [i : ComputableUnivLE.{max u v, v}] : ComputableUnivLE.{u, v} where
  Lift α := i.Lift (ULift α)
  up x := i.up (ULift.up x)
  down x := ULift.down (i.down x)
  up_down {_ _} := by
    simp only [ULift.up_down]
    rw [ComputableUnivLE.up_down]
  down_up := by
    simp [ULift.down_up, ComputableUnivLE.down_up]

instance ComputableUnivLE.zero : ComputableUnivLE.{0, u} := inferInstance

def ComputableUnivLE.trans.{v} [iuv : ComputableUnivLE.{u, v}] [ivw : ComputableUnivLE.{v, w}] : ComputableUnivLE.{u, w} where
  Lift α := α |> iuv.Lift |> ivw.Lift
  up x := x |> iuv.up |> ivw.up
  down x := x |> ivw.down |> iuv.down
  up_down := by simp [ComputableUnivLE.up_down]
  down_up := by simp [ComputableUnivLE.down_up]

class ComputableSmall.{v, u} (α : Type u) where
  Lift : Type v
  up : α → Lift
  down : Lift → α
  up_down : ∀ {a}, up (down a) = a
  down_up : ∀ {a}, down (up a) = a

@[always_inline, inline]
def ComputableSmall.Lift.down {α : Type u} [ComputableSmall α] : ComputableSmall.Lift α → α :=
  ComputableSmall.down

instance [ComputableUnivLE.{u, v}] {α} : ComputableSmall.{v, u} α where
  Lift := ComputableUnivLE.Lift α
  up := ComputableUnivLE.up
  down := ComputableUnivLE.down
  up_down := ComputableUnivLE.up_down
  down_up := ComputableUnivLE.down_up

@[always_inline, inline]
def ComputableSmall.equiv [ComputableSmall.{v} α] (f : α → β) (g : β → α)
    (hfg : ∀ {a}, f (g a) = a) (hgf : ∀ {a}, g (f a) = a) : ComputableSmall.{v} β where
  Lift := ComputableSmall.Lift (α := α)
  up x := ComputableSmall.up (g x)
  down x := f (ComputableSmall.down x)
  up_down := by simp [hgf, ComputableSmall.up_down]
  down_up := by simp [hfg, ComputableSmall.down_up]

section Tests

universe u v

#guard_msgs in
example := inferInstanceAs ComputableUnivLE.{0, u}

#guard_msgs in
example := inferInstanceAs ComputableUnivLE.{0, 1}

#guard_msgs in
example := inferInstanceAs ComputableUnivLE.{1, u + 1}

#guard_msgs in
example := inferInstanceAs ComputableUnivLE.{u, max u v}

#guard_msgs in
example := inferInstanceAs ComputableUnivLE.{u + 1, max u v + 1}

/--
error: failed to synthesize
  ComputableUnivLE

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example [ComputableUnivLE.{u, v}] [ComputableUnivLE.{u', v}] := inferInstanceAs ComputableUnivLE.{max u u', v}

end Tests
