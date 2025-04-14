/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Notation
import Init.Tactics

def ContT.{u} (m : Type w → Type w') (α : Type w) (β : Type u) := (β → m α) → m α

variable {m : Type w → Type w'}

@[always_inline, inline]
def ContT.run [Pure m] {α : Type w} (x : ContT m α α) := x pure

@[always_inline, inline]
def ContT.mapH {α : Type w} (f : β → γ) (x : ContT m α β) : ContT m α γ :=
  (x <| · ∘ f)

@[always_inline, inline]
def ContT.eval [Bind m] {α : Type w} (x : m α) : ContT m β α :=
  (x >>= .)

instance [Monad m] : Monad (ContT m α) where
  pure x h := h x
  bind x f h := x (f · h)

instance [Monad m] : MonadLift m (ContT m α) where
  monadLift x f := x >>= f

def Cont (α : Type u) (β : Type v) := (β → α) → α

instance : Monad (Cont α) where
  pure x h := h x
  bind x f h := x (f · h)

@[always_inline, inline]
def Cont.bindH {α : Type w} (x : Cont α β) (f : β → Cont α β') : Cont α β' :=
  fun h => x (f · h)

@[always_inline, inline]
def Cont.run {α : Type w} (x : Cont α α) := x id
