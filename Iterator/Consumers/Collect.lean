import Iterator.Wrapper

-- @[inline]
-- def Iter.toArrayH {α : Type u} {m : Type w → Type w'} [Monad m] {β : Type v}
--     {_ : Iterator α m β} [Finite α m] (it : Iter (α := α) m β) : m (Array β) :=
--   (CodensityT.eval <| go it #[]).mapH ComputableSmall.down
-- where
--   @[specialize]
--   go [Monad m] [Finite α m] it a : m (ComputableSmall.Lift.{w} (Array β)) := do
--     let step ← it.stepH.mapH (·.lift) |>.run
--     match step with
--       | .yield it' b _ => go it' (a.push <| ComputableSmall.down b)
--       | .skip it' _ => go it' a
--       | .done _ => return ComputableSmall.up a
--   termination_by it.terminationByFinite

section ToArray

@[always_inline, inline]
def Iter.DefaultConsumers.toArrayMapped {α : Type u} {m : Type w → Type w'} [Monad m] {β : Type v}
    {instIt : Iterator α m β} [Finite α m] {γ : Type w} (f : β → m γ) (it : Iter (α := α) m β) : m (Array γ) :=
  go it #[]
where
  @[specialize]
  go [Monad m] [Finite α m] (it : Iter (α := α) m β) a := do
    match (← it.stepH).inflate with
    | .yield it' b _ => go it' (a.push (← f b))
    | .skip it' _ => go it' a
    | .done _ => return a
  termination_by it.terminationByFinite

class IteratorToArray (α : Type u) (m : Type w → Type w') [Iterator α m β] where
  toArrayMapped : ∀ {γ : Type w}, (β → m γ) → Iter (α := α) m β → m (Array γ)

class LawfulIteratorToArray (α : Type u) (m : Type w → Type w') [Monad m] [Iterator α m β] [IteratorToArray α m] where
  finite : Finite α m
  lawful : ∀ γ, IteratorToArray.toArrayMapped (α := α) (m := m) (β := β) (γ := γ) =
    Iter.DefaultConsumers.toArrayMapped (α := α) (m := m) (γ := γ)

instance (α : Type u) (m : Type w → Type w') [Monad m] [Iterator α m β] [IteratorToArray α m]
    [LawfulIteratorToArray α m] : Finite α m :=
  LawfulIteratorToArray.finite

def IteratorToArray.defaultImplementation {α : Type u} {m : Type w → Type w'}
    [Monad m] [Iterator α m β] [Finite α m] : IteratorToArray α m where
  toArrayMapped := Iter.DefaultConsumers.toArrayMapped

instance (α : Type u) (m : Type w → Type w') [Monad m] [Iterator α m β] [IteratorToArray α m]
    [Monad m] [Iterator α m β] [Finite α m] :
    haveI : IteratorToArray α m := .defaultImplementation
    LawfulIteratorToArray α m :=
  letI : IteratorToArray α m := .defaultImplementation
  ⟨inferInstance, fun _ => rfl⟩

@[always_inline, inline]
def Iter.toArray {α : Type u} {m : Type v → Type w} {β : Type v} [Monad m]
    {_ : Iterator α m β} (it : Iter (α := α) m β) [IteratorToArray α m]: m (Array β) :=
  IteratorToArray.toArrayMapped pure it

end ToArray

@[inline]
def Iter.reverseToList {α : Type u} {m : Type v → Type w} [Monad m] {β : Type v}
    {_ : Iterator α m β} [Finite α m] (it : Iter (α := α) m β) : m (List β) :=
  go it []
where
  @[specialize]
  go [Finite α m] it bs := do
    match ← it.step with
    | .yield it' b _ => go it' (b :: bs)
    | .skip it' _ => go it' bs
    | .done _ => return bs
  termination_by it.terminationByFinite

@[inline]
def Iter.toList {α : Type u} {m : Type v → Type w} [Monad m] {β : Type v}
    {_ : Iterator α m β} (it : Iter (α := α) m β) [IteratorToArray α m] : m (List β) :=
  Array.toList <$> Iter.toArray it
