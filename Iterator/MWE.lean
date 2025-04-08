inductive Step (α β) where
| yield : (it : α) → (b : β) → Step α β
| skip : (a : α) → Step α β
| done : Step α β

class Iterator (α : Type u) (β : outParam (Type v)) where
  step : (it : α) → { s : Step α β // True }

structure ListIterator (α : Type u) where
  list : List α

instance : Iterator (ListIterator α) α where
  step
    | { list := .nil } => ⟨.done, sorry⟩
    | { list := x :: xs } => ⟨.yield { list := xs } x, sorry⟩

@[inline]
def List.iter {α} (l : List α) : ListIterator α :=
  ⟨l⟩

@[inline]
def Iteration.instIterator (stepFn : α → { s : (Step α β) // True }) : Iterator α β where
  step it := (match stepFn it with
    | ⟨.yield it' b, _⟩ => ⟨.yield it' b, sorry⟩
    | ⟨.skip it', _⟩ => ⟨.skip it', sorry⟩
    | ⟨.done, _⟩ => ⟨.done, sorry⟩)

structure MyIterator (α β α' : Type) [Iterator α β] (f : β → α') where
  inner : Option α'

instance {α β α' β' : Type} [Iterator α β] [Iterator α' β'] (f : β → α') : Iterator (MyIterator α β α' f) β' :=
  Iteration.instIterator fun
    | ⟨none⟩ => ⟨.done, sorry⟩
    | ⟨some it⟩ => ⟨match Iterator.step it with
                              | ⟨.yield it' b, _⟩ => .yield ⟨it'⟩ b
                              | _ => .done, sorry⟩

set_option trace.compiler.ir.result true in
def testMyIterator (l : List (List Nat)) : Nat :=
  go (MyIterator.mk (α := ListIterator (List Nat)) (f := List.iter) (inner := none)) 0
where
  @[specialize]
  go it acc :=
    match Iterator.step it with
    | ⟨.yield it' n, _⟩ => go it' (acc + n)
    | ⟨.skip it', _⟩ => go it' acc
    | ⟨.done, _⟩ => acc
  termination_by it
  decreasing_by all_goals sorry
