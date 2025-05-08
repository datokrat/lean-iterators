/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.UnivLE
import Init.System.IO

/-!
This file showcases a technique that allows to efficiently extend arbitrary monads to
arbitrary universes.

There's a caveat to saying "efficiently":
* The base monad is bundled together with a `Prop` and a proof. The latter two are erased at runtime
  as far as I can tell. However, Since this monad is not a function type but a structure,
  it should only be used in functions that are inlined, especially not in recursive ones.
* We occasionally need to insert `map` applications where the function will be compiled to the identity.
  Unfortunately, these currently aren't always optimized away, see the example below with the IO monad.
-/

@[unbox]
structure HetT (m : Type w → Type w') (α : Type u) where
  property : α → Prop
  small : Small.{w} (Subtype property)
  computation : m (USquash (Subtype property))

instance (m : Type w → Type w') [Functor m] : MonadLift m (HetT m) where
  monadLift x := ⟨fun _ => True, inferInstance, (fun x => .deflate ⟨x, True.intro⟩) <$> x⟩

def HetT.liftSquashed {m : Type w → Type w'} {α : Type u} [Functor m] [Small.{w} α] (x : m (USquash α)) :
    HetT m α :=
  ⟨fun _ => True, sorry, (fun x => .deflate ⟨x.inflate, True.intro⟩) <$> x⟩

@[always_inline, inline]
protected def HetT.mapH {m : Type w → Type w'} [Functor m] {α : Type u} {β : Type v}
    (f : α → β) (x : HetT m α) : HetT m β :=
  ⟨fun b => ∃ a : Subtype x.property, f a.1 = b, sorry,
    (fun a => .deflate ⟨f (a.inflate (small := _)).val, _, rfl⟩ (small := _)) <$> x.computation⟩

@[always_inline, inline]
protected def HetT.bindH {m : Type w → Type w'} [Monad m] {α : Type u} {β : Type v} (x : HetT m α) (f : α → HetT m β) : HetT m β :=
  ⟨fun b => ∃ a, x.property a ∧ (f a).property b, sorry,
    x.computation >>= fun a => letI a := a.inflate (small := _);
      (fun b => letI b := b.inflate (small := _);
        .deflate (small := _) <| ⟨b.val, a.val, a.property, b.property⟩) <$> (f a).computation⟩

@[always_inline, inline]
protected def HetT.pbindH {m : Type w → Type w'} [Monad m] {α : Type u} {β : Type v} (x : HetT m α)
    (f : Subtype x.property → HetT m β) : HetT m β :=
  ⟨fun b => ∃ a, (f a).property b, sorry,
    x.computation >>= fun a => letI a := a.inflate (small := _);
      (fun b => letI b := b.inflate (small := _);
        .deflate (small := _) <| ⟨b.val, a, b.property⟩) <$> (f a).computation⟩

@[always_inline, inline]
protected def HetT.liftMapH {m : Type w → Type w'} [Monad m] {α : Type w} {β : Type v}
    (f : α → β) (x : m α) : HetT m β :=
  ⟨fun b => ∃ a, f a = b, sorry, (fun a => .deflate ⟨f a, a, rfl⟩ (small := _)) <$> x⟩

@[always_inline, inline]
def HetT.run {m : Type w → Type w'} [Monad m] {α : Type w} (x : HetT m α) : m α :=
  (fun a => (a.inflate (small := _)).val) <$> x.computation

instance {m : Type w → Type w'} [Monad m] : Monad (HetT.{w, w', u} m) where
  pure x := ⟨fun y => x = y, sorry, pure <| .deflate (small := _) ⟨x, rfl⟩⟩
  bind x f := x.bindH f

@[simp]
theorem HetT.property_mapH {m : Type w → Type w'} [Functor m] {α : Type u} {β : Type v}
    {x : HetT m α} {f : α → β} {b : β} :
    (x.mapH f).property b ↔ (∃ a, f a = b ∧ x.property a) := by
  simp only [HetT.mapH]
  apply Iff.intro
  · rintro ⟨⟨a, ha⟩, h⟩
    exact ⟨a, h, ha⟩
  · rintro ⟨a, h, ha⟩
    exact ⟨⟨a, ha⟩, h⟩

@[simp]
theorem HetT.computation_mapH {m : Type w → Type w'} [Functor m] {α : Type u} {β : Type v}
    {x : HetT m α} {f : α → β} {b : β} :
    (x.mapH f).computation = (fun a => .deflate ⟨_, a.inflate (small := _), rfl⟩ (small := _)) <$> x.computation :=
  rfl

set_option trace.compiler.ir.result true in
def test : IO Unit := do
  IO.println "Hi"

set_option trace.compiler.ir.result true in
def test' : HetT IO Unit := HetT.run do
  IO.println "Hi"

set_option trace.compiler.ir.result true in
def aaa : Nat := Id.run <| HetT.run do
  let x ← (pure 5 : HetT Id Nat).bindH (fun x => pure <| ULift.up.{1} x) |>.bindH (fun x => pure x.down)
  let y ← pure 7
  return x + y
