/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.RCases
import Init.Core
import Init.Control.Id
import Init.Control.Lawful
import Init.System.IO

def satisfies₁ {m α} [Monad m] (x : m α) (p : α → Prop) :=
  ∀ (f : α → m α) (_ : DecidablePred p), (bind x f = bind x (fun a => if p a then f a else pure a))

def satisfies₂ {m α} [Monad m] (x : m α) (p : α → Prop) :=
  ∃ x' : m { a // p a }, x = Functor.map Subtype.val x'

def memM {m α} [Monad m] (a : α) (x : m α) : Prop :=
  ∀ (f g : α → m α), bind x f = bind x g → f a = g a

def satisfies₃ {m α} [Monad m] (x : m α) (p : α → Prop) :=
  ∀ a, memM a x → p a

class MonadAttach (m) [Monad m] where
  attach (t : m α) (p : α → Prop) (h : satisfies₃ t p) : m { a // p a }
  map_attach {t : m α} {p : α → Prop} {h} : Functor.map Subtype.val (attach t p h) = t

instance : MonadAttach Id where
  attach t _ h := ⟨t, h t fun _ _ h' => h'⟩
  map_attach := rfl

@[simp]
theorem Id.satisfies₃_iff {α} {x : α} {p} :
    satisfies₃ (m := Id) x p ↔ p x := by
  simp [satisfies₃, memM]
  sorry

theorem satisfies₁_of_satisfies₂ {m α} [Monad m] [LawfulMonad m] (x : m α) (p : α → Prop)
    (h : satisfies₂ x p) : satisfies₁ x p := by
  rw [satisfies₁, satisfies₂] at *
  obtain ⟨x', hx'⟩ := h
  simp [hx', Subtype.property]

def fix {m : Type u → Type u} [Monad m] [WellFoundedRelation α]
    [DecidableRel (WellFoundedRelation.rel (α := α))] (f : α → m α) (a : α) : m α :=
  bind (f a) (fun a' => if WellFoundedRelation.rel a' a then fix f a' else pure a')
termination_by a

def fix_iter {m} [Monad m] [LawfulMonad m] (f : α → m α) [WellFoundedRelation α]
    [DecidableRel (WellFoundedRelation.rel (α := α))] (h : ∀ a, satisfies₁ (f a) (WellFoundedRelation.rel · a)) (a : α) :
    fix f a = bind (f a) (fun a' => fix f a') := by
  rw [fix]
  conv => rhs; rw [h]

def fix₂ {m : Type u → Type u} [Monad m] [wfr : WellFoundedRelation α] (f : (a : α) → m { a' // wfr.rel a' a }) (a : α) : m α :=
  bind (f a) (fun a' => fix₂ f a'.val)
termination_by a
decreasing_by exact a'.property

def fixAttach {m} [Monad m] [MonadAttach m] [wfr : WellFoundedRelation α] (f : α → m α) (h : ∀ a, satisfies₃ (f a) (wfr.rel · a)) (a : α) :
    m α :=
  bind (MonadAttach.attach (f a) (wfr.rel · a) (h a)) (fun a' => fixAttach f h a'.val)
termination_by a
decreasing_by exact a'.property
