import Iterator.Basic

-- structure FiniteOfType (α : Type u) [Iterator α β] where
--   inner : α
--   finite : Finite inner := by infer_instance

-- instance [Iterator α β] : Iterator (FiniteOfType α) β where
--   step it := match Iterator.step it.inner with
--     | .yield it' x => .yield ⟨it', sorry⟩ x
--     | .skip it' => .skip ⟨it', sorry⟩
--     | .done => .done

-- instance [Iterator α β] (it : FiniteOfType α) : Finite it where
--   finite := sorry

-- @[inline]
-- def attachFinite [Iterator α β] (it : α) [Finite it] :
--     FiniteOfType α :=
--   { inner := it }
