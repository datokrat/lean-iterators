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

def IterationT.Plausible {m : Type w → Type w'} {γ : Type u} (x : IterationT m γ) : Type u :=
  { c : γ // x.property c }

def IterationT.Plausible.copy {m : Type w → Type w'} {γ : Type u} {s t : IterationT m γ} (h : s = t)
    (x : s.Plausible) : t.Plausible :=
  ⟨x.1, h ▸ x.2⟩

def IterationT.Plausible.copy_rfl {m : Type w → Type w'} {γ : Type u} {s : IterationT m γ}
    {x : s.Plausible} :
    x.copy rfl = x := rfl

theorem plausible_eq_copy {m : Type w → Type w'} {γ : Type u} {s t : IterationT m γ} (h : s = t) :
    s.computation = (IterationT.Plausible.copy h.symm ·) <$> t.computation := by
  cases h
  simp  [IterationT.Plausible.copy_rfl, CodensityT.map_eq_mapH, CodensityT.mapH_id']

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
def IterationT.mapH {γ : Type u} {m : Type w → Type w'}
    {δ : Type v}
    (f : γ → δ)
    (t : IterationT m γ) : IterationT m δ :=
  { property d := ∃ c, d = f c ∧ t.property c,
    computation := t.computation.mapH fun c => ⟨f c.1, c.1, rfl, c.2⟩ }

theorem IterationT.map_eq_mapH {γ δ : Type u} {m : Type w → Type w'} {f : γ → δ} {t : IterationT m γ} :
    f <$> t = t.mapH f := rfl

theorem IterationT.mapH_id {γ : Type u} {m : Type w → Type w'} {t : IterationT m γ} :
    t.mapH id = t := by
  simp only [mapH, id]
  let prop d := ∃ c, d = c ∧ t.property c
  have : prop = t.property := by
    ext c
    exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨c, rfl, h⟩⟩
  let trafo (p : { p : γ → Prop // p = t.property }) : IterationT m γ :=
    { property := p.1
      computation := t.computation.mapH (fun x => ⟨x.val, by rw [p.2]; exact x.2⟩) }
  exact (congrArg trafo (Subtype.eq_iff.mpr this : ⟨prop, this⟩ = ⟨t.property, rfl⟩))

theorem IterationT.mapH_id' {γ : Type u} {m : Type w → Type w'} {t : IterationT m γ} :
    t.mapH (·) = t :=
  IterationT.mapH_id

theorem IterationT.mapH_mapH {γ : Type u} {δ : Type u'} {ε : Type u''} {m : Type w → Type w'}
    {f : γ → δ} {g : δ → ε} {t : IterationT m γ} :
    (t.mapH f).mapH g = t.mapH (f · |> g) := by
  simp only [mapH, CodensityT.mapH_mapH]
  let prop d := ∃ c, d = g (f c) ∧ t.property c
  let prop' d := ∃ c, d = g c ∧ ∃ c', c = f c' ∧ t.property c'
  have : prop = prop' := by
    ext y
    simp only [prop, prop']
    apply Iff.intro
    · rintro ⟨c, rfl, h⟩
      exact ⟨f c, rfl, c, rfl, h⟩
    · rintro ⟨c, rfl, c', rfl, h⟩
      exact ⟨c', rfl, h⟩
  let trafo (p : { p : ε → Prop // p = prop }) : IterationT m ε :=
    { property := p.1
      computation := t.computation.mapH (fun x => ⟨(g (f x.val)), by rw [p.2]; exact ⟨x.1, rfl, x.2⟩⟩) }
  have := congrArg trafo (Subtype.eq_iff.mpr this : ⟨prop, rfl⟩ = ⟨prop', this.symm⟩)
  refine this.symm.trans ?_
  simp [trafo, prop]

theorem IterationT.property_mapH {γ : Type u} {δ : Type u'} {m : Type w → Type w'} {t : IterationT m γ}
    {x : γ} (f : γ → δ) (h : t.property x) : (t.mapH f).property (f x) :=
  ⟨x, rfl, h⟩

@[always_inline, inline]
def IterationT.Plausible.map {m : Type w → Type w'} {γ : Type u} {δ : Type u'}
    {t : IterationT m γ} (f : γ → δ) (x : t.Plausible) : (t.mapH f).Plausible :=
  ⟨f x.1, x.1, rfl, x.2⟩

@[always_inline, inline]
def IterationT.bindH {m : Type w → Type w'} {γ : Type u} {δ : Type v}
    (t : IterationT m γ) (f : γ → IterationT m δ) : IterationT m δ :=
  { property d := ∃ c, (f c).property d ∧ t.property c
    computation := t.computation.bindH fun c => (f c.1).computation.mapH fun d => ⟨d.1, c.1, d.2, c.2⟩}

theorem IterationT.mapH_eq_bindH {γ : Type u} {δ : Type u'} {m : Type w → Type w'} {f : γ → δ}
    {t : IterationT m γ} :
    t.mapH f = t.bindH (pure <| f ·) := rfl

@[always_inline, inline]
def IterationT.liftInnerMonad {γ : Type w} {m : Type w → Type w'} [Pure m] (n : Type w → Type w'') [Monad n] [MonadLift m n] (t : IterationT m γ) :
    IterationT n γ :=
  { property := t.property
    computation := monadLift t.computation.run }
