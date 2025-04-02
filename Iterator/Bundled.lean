/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic

-- structure BundledIterator (β : Type v) where
--   α : Type u
--   it : α
--   inst : Iterator α β

-- def toBundledIterator [Iterator α β] (it : α) : BundledIterator β :=
--   ⟨α, it, inferInstance⟩

-- structure FiniteIterator (β : Type v) extends BundledIterator β where
--   finite : Finite it

-- def toFiniteIterator [Iterator α β] (it : α) [Finite it] :
--     FiniteIterator β :=
--   ⟨toBundledIterator it, inferInstanceAs (Finite it)⟩

-- instance (it : BundledIterator β) : Iterator it.α β := it.inst

-- instance : Iterator (BundledIterator β) β where
--   step it := match Iterator.step it.it with
--     | .yield it' x => .yield ⟨it.α, it', it.inst⟩ x
--     | .skip it' => .skip ⟨it.α, it', it.inst⟩
--     | .done => .done

-- instance (it : FiniteIterator β) : Finite it.toBundledIterator where
--   finite := sorry

-- instance : Iterator (FiniteIterator β) β where
--   step it := match h : it.inst.step it.it with
--     | .yield it' x => .yield ⟨⟨it.α, it', it.inst⟩, it.finite.yield h⟩ x
--     | .skip it' => .skip ⟨⟨it.α, it', it.inst⟩, it.finite.skip h⟩
--     | .done => .done

-- instance (it : FiniteIterator β) : Finite it where
--   finite := sorry
