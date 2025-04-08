variable {α : Type u} {β : Type v}

inductive Step (α β) where
| yield : (it : α) → (b : β) → Step α β
| skip : (a : α) → Step α β
| done : Step α β

class Iterator (α : Type u) (β : outParam (Type v)) where
  step : (it : α) → { s : Step α β // match s with
      | .yield it' b => True
      | .skip it' => True
      | .done => True }

abbrev Step.for {α β} [Iterator α β] (it : α) := { s : Step α β // match s with
    | .yield it' b => True
    | .skip it' => True
    | .done => True }

structure Wrapper (α β) [Iterator α β] where
  inner : α

@[inline]
def toWrapper [Iterator α β] (it : α) : Wrapper α β :=
  ⟨it⟩

instance [Iterator α β] : Iterator (Wrapper α β) β where
  step it := match Iterator.step it.inner with
    | ⟨.yield it' x, h⟩ => ⟨.yield ⟨it'⟩ x, h⟩
    | ⟨.skip it', h⟩ => ⟨.skip ⟨it'⟩, h⟩
    | ⟨.done, h⟩ => ⟨.done, h⟩

structure ListIterator (α : Type u) where
  list : List α

instance : Iterator (ListIterator α) α where
  step
    | { list := .nil } => ⟨.done, sorry⟩
    | { list := x :: xs } => ⟨.yield { list := xs } x, sorry⟩

@[inline]
def List.iter {α} (l : List α) : Wrapper (ListIterator α) α :=
  toWrapper { list := l }

structure Iteration (γ : Type u) where
  prop : γ → Prop
  elem : { c // prop c }

@[inline]
def Iteration.instIterator (stepFn : α → Iteration (Step α β)) : Iterator α β where
  step it := (match (stepFn it).elem with
    | ⟨.yield it' b, h⟩ => ⟨.yield it' b, sorry⟩
    | ⟨.skip it', h⟩ => ⟨.skip it', sorry⟩
    | ⟨.done, h⟩ => ⟨.done, sorry⟩)

structure MyIterator (α β α' : Type) [Iterator α β] (f : β → α') where
  inner : Option α'

instance {α β α' β' : Type} [Iterator α β] [Iterator α' β'] (f : β → α') : Iterator (MyIterator α β α' f) β' :=
  Iteration.instIterator fun
    | ⟨none⟩ => { prop := sorry, elem := ⟨.done, sorry⟩ }
    | ⟨some it⟩ => { prop d := d = d
                     elem := ⟨match Iterator.step it with
                              | ⟨.yield it' b, _⟩ => .yield ⟨it'⟩ b
                              | _ => .done, sorry⟩ }

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
