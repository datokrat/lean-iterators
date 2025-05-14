/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.System.IO

@[unbox]
structure HetT (m : Type w → Type w') (α : Type w) where
  property : α → Prop
  computation : m (Subtype property)

instance (m : Type w → Type w') [Functor m] : MonadLift m (HetT m) where
  monadLift x := ⟨fun _ => True, (fun x => ⟨x, True.intro⟩) <$> x⟩

@[always_inline, inline]
def HetT.lift {α : Type w} {m : Type w → Type w'} [Functor m] (x : m α) :
    HetT m α :=
  x

@[always_inline, inline]
protected def HetT.mapH {m : Type w → Type w'} [Functor m] {α : Type w} {β : Type w}
    (f : α → β) (x : HetT m α) : HetT m β :=
  ⟨fun b => ∃ a : Subtype x.property, f a.1 = b,
    (fun a => ⟨f a.val, _, rfl⟩) <$> x.computation⟩

@[always_inline, inline]
protected def HetT.bindH {m : Type w → Type w'} [Monad m] {α : Type w} {β : Type w} (x : HetT m α) (f : α → HetT m β) : HetT m β :=
  ⟨fun b => ∃ a, x.property a ∧ (f a).property b,
    x.computation >>= fun a =>
      (fun b =>
        ⟨b.val, a.val, a.property, b.property⟩) <$> (f a).computation⟩

@[always_inline, inline]
protected def HetT.pbind {m : Type w → Type w'} [Monad m] {α : Type w} {β : Type w} (x : HetT m α)
    (f : Subtype x.property → HetT m β) : HetT m β :=
  ⟨fun b => ∃ a, (f a).property b,
    x.computation >>= fun a => (fun b => ⟨b.val, a, b.property⟩) <$> (f a).computation⟩

@[always_inline, inline]
protected def HetT.liftMapH {m : Type w → Type w'} [Monad m] {α : Type w} {β : Type w}
    (f : α → β) (x : m α) : HetT m β :=
  ⟨fun b => ∃ a, f a = b, (fun a => ⟨f a, a, rfl⟩) <$> x⟩

@[always_inline, inline]
def HetT.run {m : Type w → Type w'} [Monad m] {α : Type w} (x : HetT m α) : m α :=
  (fun a => a.val) <$> x.computation

instance {m : Type w → Type w'} [Functor m] : Functor (HetT m) where
  map f x := ⟨fun b => ∃ a, f a = b, (fun b => ⟨f b.1, b.1, rfl⟩) <$> x.computation ⟩

instance {m : Type w → Type w'} [Monad m] : Monad (HetT m) where
  pure x := ⟨fun y => x = y, pure <| ⟨x, rfl⟩⟩
  bind x f := ⟨fun b => ∃ a, (f a).property b,
      x.computation >>= fun a => (fun b => ⟨b.val, a, b.property⟩) <$> (f a).computation⟩

@[simp]
theorem HetT.computation_pure {m : Type w → Type w'} [Monad m] {α : Type w}
    {x : α} :
    (pure x : HetT m α).computation = pure ⟨x, rfl⟩ :=
  rfl

@[simp]
theorem HetT.property_pure {m : Type w → Type w'} [Monad m] {α : Type w}
    {x : α} :
    (pure x : HetT m α).property = (x = ·) :=
  rfl

theorem HEq.congrArg {α : Sort u} {β : α → Type v} (f : (a : α) → β a) {a a'} (h : a = a') :
    HEq (f a) (f a') := by
  cases h; rfl

theorem HEq.congrArg₂ {α : Sort u} {β : α → Type v} {γ : (a : α) → (b : β a) → Sort w}
    (f : (a : α) → (b : β a) → γ a b)
    {α α' a a'} (h : α = α') (h' : HEq a a') : HEq (f α a) (f α' a') := by
  cases h; cases h'; rfl

theorem HEq.congrArg₃ {α : Sort u} {β : (a : α) → Sort v} {γ : (a : α) → (b : β a) → Sort w}
    {δ : (a : α) → (b : β a) → (c : γ a b) → Sort x}
    (f : (a : α) → (b : β a) → (c : γ a b) → δ a b c)
    {a a' b b' c c'} (h₁ : a = a') (h₂ : HEq b b') (h₃ : HEq c c') : HEq (f a b c) (f a' b' c') := by
  cases h₁; cases h₂; cases h₃; rfl

theorem HEq.congrArg₄ {α : Sort u} {β : (a : α) → Sort v} {γ : (a : α) → (b : β a) → Sort w}
    {δ : (a : α) → (b : β a) → (c : γ a b) → Sort x} {ε : (a : α) → (b : β a) → (c : γ a b) → (d : δ a b c) → Sort y}
    (f : (a : α) → (b : β a) → (c : γ a b) → (d : δ a b c) → ε a b c d)
    {a a' b b' c c' d d'} (h₁ : a = a') (h₂ : HEq b b') (h₃ : HEq c c') (h₄ : HEq d d') : HEq (f a b c d) (f a' b' c' d') := by
  cases h₁; cases h₂; cases h₃; cases h₄; rfl

@[simp]
protected theorem HetT.mapH_pure {m : Type w → Type w'} [Monad m] [LawfulMonad m] {α : Type w} {β : Type w}
    {f : α → β} {a : α} :
    (pure a : HetT m α).mapH f = pure (f a) := by
  simp [HetT.mapH, pure, mk.injEq, map_pure]
  apply HEq.congrArg₂ (f := fun α (a : α) => (pure a : m _)) (by simp)
  apply HEq.congrArg₂ (f := fun α (a : α) => a)
  · simp
  · apply HEq.congrArg₄ fun β (p : β → Prop) (x : β) (h : p x) => Subtype.mk x h
    · rfl
    · simp
    · rfl
    · simp

@[simp]
theorem HetT.property_mapH {m : Type w → Type w'} [Functor m] {α : Type w} {β : Type w}
    {x : HetT m α} {f : α → β} {b : β} :
    (x.mapH f).property b ↔ (∃ a, f a = b ∧ x.property a) := by
  simp only [HetT.mapH]
  apply Iff.intro
  · rintro ⟨⟨a, ha⟩, h⟩
    exact ⟨a, h, ha⟩
  · rintro ⟨a, h, ha⟩
    exact ⟨⟨a, ha⟩, h⟩

@[simp]
theorem HetT.computation_mapH {m : Type w → Type w'} [Functor m] {α : Type w} {β : Type w}
    {x : HetT m α} {f : α → β} :
    (x.mapH f).computation = (fun a => ⟨_, a, rfl⟩) <$> x.computation :=
  rfl
