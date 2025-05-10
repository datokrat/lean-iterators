/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Core
import Init.Ext
import Init.SimpLemmas
import Init.NotationExtra
import Init.Classical

universe u v

class ComputableSmall (α : Type v) where
  Target : Type u
  deflate : α → Target
  inflate : Target → α
  deflate_inflate : ∀ {a}, deflate (inflate a) = a
  inflate_deflate : ∀ {a}, inflate (deflate a) = a

class Small (α : Type v) : Prop where
  h : Nonempty (ComputableSmall.{u} α)

noncomputable def ComputableSmall.choose (α : Type v) [small : Small.{u} α] : ComputableSmall.{u} α :=
  haveI : Nonempty (ComputableSmall.{u} α) := Small.h
  Classical.ofNonempty (α := ComputableSmall.{u} α)

variable {α : Type v} {β : Type u}

structure USquash (α : Type v) [small : Small.{u} α] where
  mk' ::
  inner : (ComputableSmall.choose α).Target

private unsafe def USquash.unsafeDeflate [Small.{u} α] : α → USquash.{u} α := unsafeCast
private unsafe def USquash.unsafeInflate [Small.{u} α] : USquash.{u} α → α := unsafeCast

@[implemented_by USquash.unsafeDeflate]
noncomputable def USquash.deflate [small : Small.{u} α] (x : α) : USquash.{u} α := USquash.mk' (ComputableSmall.choose α |>.deflate x)

@[implemented_by USquash.unsafeInflate]
noncomputable def USquash.inflate [small : Small.{u} α] (x : USquash.{u} α) : α := ComputableSmall.choose α |>.inflate x.inner

@[simp]
theorem USquash.deflate_inflate {_ : Small.{u} α} {x : USquash.{u} α} :
    USquash.deflate x.inflate = x := by
  simp [deflate, inflate, ComputableSmall.deflate_inflate]

@[simp]
theorem USquash.inflate_deflate {_ : Small.{u} α} {x : α} :
    (USquash.deflate.{u} x).inflate = x := by
  simp [deflate, inflate, ComputableSmall.inflate_deflate]

theorem USquash.inflate.inj {_ : Small.{u} α} {x y : USquash α} (h : x.inflate = y.inflate) : x = y := by
  rw [← deflate_inflate (x := x), ← deflate_inflate (x := y), h]

attribute [deprecated "never use!" (since := "2025-04-28")]
  USquash.inner USquash.mk'

class UnivLE where
  small : ∀ α : Type u, Small.{v} α

instance [UnivLE.{u, v}] {α : Type u} : Small.{v} α := UnivLE.small α

instance UnivLE.self : UnivLE.{u, u} where
  small α := ⟨⟨{
    Target := α
    deflate := id
    inflate := id
    deflate_inflate := rfl
    inflate_deflate := rfl }⟩⟩

set_option pp.universes true in
instance UnivLE.ofMax [i : UnivLE.{max u v, v}] : UnivLE.{u, v} where
  small α := ⟨⟨{
    Target := ComputableSmall.choose.{v} (ULift.{v} α) |>.Target
    deflate x := ComputableSmall.choose.{v} (ULift.{v} α) |>.deflate (ULift.up x)
    inflate x := ULift.down (ComputableSmall.choose.{v} (ULift.{v} α) |>.inflate x)
    deflate_inflate {_} := by simp [ULift.up_down, ComputableSmall.deflate_inflate]
    inflate_deflate {_} := by simp [ULift.down_up, ComputableSmall.inflate_deflate]
  }⟩⟩

instance UnivLE.zero : UnivLE.{0, u} := inferInstance

def ComputableUnivLE.trans [iuv : UnivLE.{u, v}] [ivw : UnivLE.{v, w}] : UnivLE.{u, w} where
  small α := ⟨⟨{
    Target := α |> (ComputableSmall.choose.{v} · |>.Target) |> (ComputableSmall.choose.{w} · |>.Target)
    deflate x := x |> (ComputableSmall.choose.{v} _).deflate |> (ComputableSmall.choose.{w} _).deflate
    inflate x := x |> (ComputableSmall.choose.{w} _).inflate |> (ComputableSmall.choose.{v} _).inflate
    deflate_inflate := by simp [ComputableSmall.deflate_inflate]
    inflate_deflate := by simp [ComputableSmall.inflate_deflate]
  }⟩⟩

instance {α : Type v} [Small.{u} α] {p : α → Prop} : Small.{u} (Subtype p) where
  h := ⟨{
    Target := Subtype (p ∘ USquash.inflate : USquash.{u} α → Prop)
    deflate x := ⟨USquash.deflate x.1, by simp [x.2]⟩
    inflate x := ⟨USquash.inflate x.1, x.2⟩
    deflate_inflate := by simp
    inflate_deflate := by simp }⟩

instance {α : Type v} [Small.{u} α] : Small.{u} (Option α) where
  h := ⟨{
    Target := Option (USquash α)
    deflate x := x.map .deflate
    inflate x := x.map USquash.inflate
    deflate_inflate {x} := by cases x <;> simp
    inflate_deflate {x} := by cases x <;> simp }⟩

def Small.small_quotient {α : Type v} [Small.{w} α] (s : Setoid α) : Small.{w} (Quotient s) where
  h :=
    letI s' : Setoid (USquash.{w} α) := {
      r x y := s.r x.inflate y.inflate,
      iseqv := {
        refl a := s.iseqv.refl a.inflate
        symm h := s.iseqv.symm h
        trans h h' := s.iseqv.trans h h' } }
    ⟨⟨Quotient s',
      Quotient.lift (Quotient.mk s' ∘ USquash.deflate) (by
          intro a b h
          apply Quotient.sound
          simp only [HasEquiv.Equiv, Setoid.r, USquash.inflate_deflate, s']
          exact h),
      Quotient.lift (Quotient.mk s ∘ USquash.inflate) (by
          intro a b h
          apply Quotient.sound
          simp only [HasEquiv.Equiv, Setoid.r, s'] at h
          exact h),
      (by
        intro a
        obtain ⟨_, rfl⟩ := Quotient.exists_rep a
        simp [Quotient.lift, Quotient.mk]),
      (by
        intro a
        obtain ⟨_, rfl⟩ := Quotient.exists_rep a
        simp [Quotient.lift, Quotient.mk])⟩⟩

instance Small.instSmall_quotient {α : Type v} [Small.{w} α] [s : Setoid α] : Small.{w} (Quotient s) :=
  Small.small_quotient s

def Small.small_domain {α : Type v} {β : Type v'} [Small.{w} α] {f : α → β}
    (h : ∀ b, ∃ a, f a = b) : Small.{w} β where
  h :=
    letI s : Setoid α := { r x y := f x = f y, iseqv := {
      refl _ := rfl
      symm h := Eq.symm h
      trans h h' := Eq.trans h h' } }
    ⟨⟨USquash <| Quotient s,
      (by
        intro b
        apply USquash.deflate
        apply Quotient.mk
        exact (h b).choose),
      (by
        refine Function.comp ?_ USquash.inflate
        apply Quotient.lift f
        exact fun _ _ => id),
      (by
        intro a
        rw [← USquash.deflate_inflate (x := a)]
        apply congrArg USquash.deflate
        generalize a.inflate = a
        obtain ⟨_, rfl⟩ := Quotient.exists_rep a
        apply Quotient.sound
        simp only [HasEquiv.Equiv, Setoid.r, Function.comp_apply, USquash.inflate_deflate, s]
        exact Exists.choose_spec (p := (f · = _)) _),
      (by
        intro a
        simp only [Quotient.lift, Quotient.mk, Function.comp_apply, USquash.inflate_deflate, s]
        exact (h a).choose_spec)⟩⟩

theorem Eq.apply_rec {α : Type u} {β : α → Type v} {γ : α → Type w} {a a' : α} (h : a = a')
    (f : ∀ a, β a → γ a) (x : β a) : f a' (h ▸ x) = h ▸ (f a x) := by
  cases h
  simp

private theorem Eq.rec_heq_self {α : Type u} {a a' : α} {motive : (a' : α) → a = a' → Type v}
    {x : motive a rfl} {h : a = a'} : HEq (Eq.rec x h : motive a' h) x := by
  cases h
  exact .refl _

instance Small.instSmall_sigma {α : Type v} {β : α → Type v'} [Small.{w} α] [∀ a, Small.{w} (β a)] : Small.{w} (Sigma β) where
  h := ⟨⟨Sigma (fun x : USquash.{w} α => USquash.{w} (β x.inflate)),
         fun | ⟨a, b⟩ => ⟨.deflate a, .deflate (USquash.inflate_deflate ▸ b)⟩,
         fun | ⟨a, b⟩ => ⟨a.inflate, b.inflate⟩,
         (by
          simp
          intro p
          ext
          · simp
          · simp [Eq.apply_rec _ (fun a => USquash.deflate)]
            exact Eq.rec_heq_self),
         (by
          simp
          intro p
          ext
          · simp
          · simp [Eq.apply_rec _ _]
            exact Eq.rec_heq_self)⟩⟩

instance Small.instProd_sigma {α : Type v} {β : Type v'} [Small.{w} α] [Small.{w} β] : Small.{w} (α × β) :=
  Small.small_domain.{_, _, w} (α := (_ : α) × β) (f := fun | ⟨a, b⟩ => (a, b)) (fun | (a, b) => ⟨⟨a, b⟩, rfl⟩)

-- @[always_inline, inline]
-- def ComputableSmall.Target.down {α : Type u} [ComputableSmall α] : ComputableSmall.Lift α → α :=
--   ComputableSmall.down

-- instance [ComputableUnivLE.{u, v}] {α} : ComputableSmall.{v, u} α where
--   Lift := ComputableUnivLE.Lift α
--   up := ComputableUnivLE.up
--   down := ComputableUnivLE.down
--   up_down := ComputableUnivLE.up_down
--   down_up := ComputableUnivLE.down_up

-- @[always_inline, inline]
-- def ComputableSmall.equiv [ComputableSmall.{v} α] (f : α → β) (g : β → α)
--     (hfg : ∀ {a}, f (g a) = a) (hgf : ∀ {a}, g (f a) = a) : ComputableSmall.{v} β where
--   Lift := ComputableSmall.Lift (α := α)
--   up x := ComputableSmall.up (g x)
--   down x := f (ComputableSmall.down x)
--   up_down := by simp [hgf, ComputableSmall.up_down]
--   down_up := by simp [hfg, ComputableSmall.down_up]

section Tests

#guard_msgs in
example := inferInstanceAs UnivLE.{0, u}

#guard_msgs in
example := inferInstanceAs UnivLE.{0, 1}

#guard_msgs in
example := inferInstanceAs UnivLE.{1, u + 1}

#guard_msgs in
example := inferInstanceAs UnivLE.{u, max u v}

#guard_msgs in
example := inferInstanceAs UnivLE.{u + 1, max u v + 1}

/--
error: failed to synthesize
  UnivLE

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example [UnivLE.{u, v}] [UnivLE.{u', v}] := inferInstanceAs UnivLE.{max u u', v}

end Tests
