/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Core
import Init.Ext
import Iterator.Cont

@[ext]
structure IterationT (m : Type w → Type w') (γ : Type u) where
  property : γ → Prop
  computation : CodensityT m { c : γ // property c }

instance : Monad (IterationT m) where
  pure a := { property b := (b = a)
              computation := pure ⟨a, rfl⟩ }
  bind x f := { property a := ∃ b, (f b).property a ∧ x.property b
                computation := do
                  let b ← x.computation
                  let a ← (f b).computation
                  return ⟨a.1, b.1, a.2, b.2⟩ }

theorem IterationT.computation_pure {m : Type w → Type w'} {γ : Type u} {a : γ} :
    (pure a : IterationT m γ).computation = pure ⟨a, rfl⟩ := rfl

instance (m) [Monad m] : MonadLift m (IterationT m) where
  monadLift t := { property := fun _ => True, computation := (⟨·, True.intro⟩) <$> t }

instance (m) [Monad m] : MonadLift (CodensityT m) (IterationT m) where
  monadLift t := { property := fun _ => True, computation := (⟨·, True.intro⟩) <$> t }

@[always_inline, inline]
def IterationT.liftWithProperty {p : γ → Prop} (t : CodensityT m { c : γ // p c }) : IterationT m γ :=
  { property := p, computation := t }

@[always_inline, inline]
def IterationT.mapH {γ : Type u} {m : Type w → Type w'} [Monad m]
    {δ : Type v}
    (f : γ → δ)
    (t : IterationT m γ) : IterationT m δ :=
  { property d := ∃ c, d = f c ∧ t.property c,
    computation := t.computation.mapH fun c => ⟨f c.1, c.1, rfl, c.2⟩ }

@[always_inline, inline]
def IterationT.bindH {m : Type w → Type w'} [Monad m] {γ : Type u} {δ : Type v}
    (t : IterationT m γ) (f : γ → IterationT m δ) : IterationT m δ :=
  { property d := ∃ c, (f c).property d ∧ t.property c
    computation := t.computation.bindH fun c => (f c.1).computation.mapH fun d => ⟨d.1, c.1, d.2, c.2⟩}

@[always_inline, inline]
def IterationT.liftInnerMonad {γ : Type w} {m : Type w → Type w'} [Pure m] (n : Type w → Type w'') [Monad n] [MonadLift m n] (t : IterationT m γ) :
    IterationT n γ :=
  { property := t.property
    computation := monadLift t.computation.run }
