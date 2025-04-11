/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/

structure OverT.{w} (m : Type v → Type v') (β : Type w) : Type max (v + 1) v' w where
  α : Type v
  el : m α
  f : α → β

@[inline]
def OverT.eval {m : Type v → Type v'} {α : Type v} (x : m α) : OverT m α :=
  { α := α, el := x, f := id }

@[inline]
def OverT.mapH {m : Type v → Type v'} {β : Type w} {β' : Type w'} (f : β → β') (x : OverT m β) :
    OverT m β' :=
  { α := x.α, el := x.el, f := f ∘ x.f }

@[inline]
def OverT.bindH {m : Type v → Type v'} [Monad m] {β : Type w} {β' : Type w'}
    (x : OverT m β) (f : β → OverT m β') :
    OverT m β' :=
    { α := (a : x.α) × (f (x.f a)).α
      el := x.el >>= (fun a => (⟨a, ·⟩) <$> (f (x.f a)).el)
      f := fun a => (f (x.f a.1)).f a.2 }

instance (m : Type v → Type v') [Pure m] : Pure (OverT.{w} m) where
  pure x := { α := PUnit, el := pure ⟨⟩, f := fun _ => x }

instance (m : Type v → Type v') : Functor (OverT.{w} m) where
  map := OverT.mapH

instance (m : Type v → Type v') [Monad m] : Monad (OverT.{w} m) where
  bind := OverT.bindH

instance (m : Type v → Type v') : MonadEval m (OverT m) where
  monadEval := OverT.eval

instance (m : Type v → Type v') (n : Type v → Type v'') [MonadEvalT m n] : MonadEvalT (OverT m) (OverT n) where
  monadEval x := { α := x.α, el := MonadEvalT.monadEval x.el, f := x.f }

instance (m : Type v → Type v') (n : Type v → Type v'') [MonadEval m n] : MonadEval (OverT m) (OverT n) where
  monadEval x := { α := x.α, el := MonadEvalT.monadEval x.el, f := x.f }
