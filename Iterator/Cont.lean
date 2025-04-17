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

def CodensityT.{u} (m : Type w → Type w') (β : Type u) := ∀ (α), (β → m α) → m α

@[always_inline, inline]
def CodensityT.run [Pure m] {α : Type w} (x : CodensityT m α) := x _ pure

@[always_inline, inline]
def CodensityT.mapH {β : Type u} {γ : Type u'} (f : β → γ) (x : CodensityT m β) : CodensityT m γ :=
  fun _ h => x _ (h ∘ f)

@[always_inline, inline]
def CodensityT.bindH {β : Type u} {γ : Type u'} (x : CodensityT m β) (f : β → CodensityT m γ) : CodensityT m γ :=
  fun _ h => x _ (f · _ h)

@[always_inline, inline]
def CodensityT.eval [Bind m] {α : Type w} (x : m α) : CodensityT m α :=
  fun _ h => x >>= h

instance : Pure (CodensityT m) where
  pure x _ h := h x

instance [Monad m] : Monad (CodensityT m) where
  pure x _ h := h x
  bind x f _ h := x _ (f · _ h)

instance [Monad m] : MonadLift m (CodensityT m) where
  monadLift x _ f := x >>= f

def Cont (α : Type u) (β : Type v) := (β → α) → α

instance : Monad (Cont α) where
  pure x h := h x
  bind x f h := x (f · h)

@[always_inline, inline]
def Cont.bindH {α : Type w} (x : Cont α β) (f : β → Cont α β') : Cont α β' :=
  fun h => x (f · h)

@[always_inline, inline]
def Cont.run {α : Type w} (x : Cont α α) := x id
