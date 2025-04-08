
variable {α : Type u} {β : Type v}

inductive IterStep (α β) (yielded : α → β → Prop) (skipped : α → Prop) (finished : Prop) where
| yield : (it : α) → (b : β) → yielded it b → IterStep α β yielded skipped finished
| skip : (a : α) → skipped a → IterStep α β yielded skipped finished
| done : finished → IterStep α β yielded skipped finished

set_option pp.all true in
def IterStep.successor {yp sp fp} : IterStep α β yp sp fp → Option α
  | .yield it _ _ => some it
  | .skip it _ => some it
  | .done _ => none

class Iterator (α : Type u) (m : outParam (Type (max u v) → Type x)) (β : outParam (Type v)) where
  yielded : α → α → β → Prop
  skipped : α → α → Prop
  finished : α → Prop
  step : (a : α) → m (IterStep α β (yielded a) (skipped a) (finished a))

section Wrapper

structure Iter (m) (β : Type v) [Iterator α m β] where
  inner : α

@[inline]
def toIter {m} [Iterator α m β] (it : α) : Iter (α := α) m β :=
  ⟨it⟩

instance {m} [Functor m] [Iterator α m β] : Iterator (Iter (α := α) m β) m β where
  yielded it it' b := Iterator.yielded it.inner it'.inner b
  skipped it it' := Iterator.skipped it.inner it'.inner
  finished it := Iterator.finished it.inner
  step it := (match · with
    | .yield it' x h => .yield ⟨it'⟩ x h
    | .skip it' h => .skip ⟨it'⟩ h
    | .done h => .done h) <$> (Iterator.step it.inner)

end Wrapper

section ListIterator

variable {m : Type u → Type u}

structure ListIterator (α : Type u) (m : Type u → Type u) where
  list : List α

instance [Pure m] : Iterator (ListIterator α m) m α where
  yielded it it' a := sorry
  skipped it it' := sorry
  finished it := sorry
  step
    | { list := .nil } => pure <| .done sorry
    | { list := x :: xs } => pure <| .yield { list := xs } x sorry

@[inline]
def List.iter {α} (l : List α) (m := Id) [Pure m] : Iter (α := ListIterator α m) m α :=
  toIter { list := l }

end ListIterator

section AbstractIteration

abbrev RawStep (α β) := IterStep α β (fun _ _ => True) (fun _ => True) True

abbrev IterStep.for {α β m} [Iterator α m β] (it : α) := IterStep α β (Iterator.yielded it) (Iterator.skipped it) (Iterator.finished it)

structure Iteration (m : Type u → Type v) (γ : Type u) where
  prop : γ → Prop
  elem : m { c // prop c }

@[inline]
def Iteration.pure {γ m} [Pure m] (c : γ) : Iteration m γ :=
  { prop c' := sorry, elem := Pure.pure ⟨c, sorry⟩ }

@[inline]
def Iteration.bind {γ δ m} [Monad m] (t : Iteration m γ) (f : γ → Iteration m δ) : Iteration m δ :=
  { prop d := d = d -- some nontrivial term (not sorry!) so that optimizations don't trigger
    elem := do (fun x => ⟨x.1, sorry⟩) <$> (f (← t.elem).val).elem }

instance (m) [Monad m] : Monad (Iteration m) where
  pure := Iteration.pure
  bind := Iteration.bind

@[inline]
def Iteration.step {α : Type u} {β : Type v} [Iterator α m β] [Functor m] (it : α) : Iteration m (IterStep.for it) :=
  { prop := sorry,
    elem := (fun step => ⟨step, sorry⟩) <$> Iterator.step it }

@[inline]
def Iteration.instIterator [Functor m] (stepFn : α → Iteration m (RawStep α β)) : Iterator α m β where
  yielded it it' b := sorry --(stepFn it).prop (.yield it' b ⟨⟩)
  skipped it it' := (stepFn it).prop (.skip it' ⟨⟩)
  finished it := (stepFn it).prop (.done ⟨⟩)
  step it := (match · with
    | ⟨.yield it' b _, h⟩ => .yield it' b sorry
    | ⟨.skip it' _, h⟩ => .skip it' h
    | ⟨.done _, h⟩ => .done h) <$> (stepFn it).elem

end AbstractIteration

section Combinators

structure FlatMap2 (α β α' : Type) [Iterator α Id β] (f : β → α') where
  it₂ : Option α'

instance {α β α' β' : Type} [Iterator α Id β] [Iterator α' Id β'] (f : β → α') : Iterator (FlatMap2 α β α' f) Id β' :=
  Iteration.instIterator fun
    | { it₂ := none } => pure <| .done ⟨⟩
    | { it₂ := some it₂ } => do
      ⟨fun _ => True, match ← { prop := sorry, elem := ⟨Iterator.step it₂, sorry⟩ } with
      | .yield it' b _ => ⟨.yield { it₂ := some it' } b ⟨⟩, sorry⟩
      | .skip it' _ => ⟨.skip { it₂ := some it' } ⟨⟩, sorry⟩
      | .done _ => ⟨.done ⟨⟩, sorry⟩⟩

end Combinators

section IR

set_option trace.compiler.ir.result true in
def testFlatMap (l : List (List Nat)) : Nat :=
  go (FlatMap2.mk (α := ListIterator (List Nat) Id) (f := List.iter) none) 0
where
  @[specialize]
  go it acc :=
    match Iterator.step it with
    | .yield it' n _ => go it' (acc + n)
    | .skip it' _ => go it' acc
    | .done _ => acc
  termination_by it
  decreasing_by
    · sorry
    · sorry

end IR
