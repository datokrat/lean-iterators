import Iterator.Basic

@[specialize]
def IterM.DefaultConsumers.forIn {m : Type w → Type w'} {n : Type w → Type w''} [Monad n] [MonadLiftT m n]
    {α : Type w} {β : Type v} {γ : Type w}
    [Iterator α m β] [Finite α m]
    (it : IterM (α := α) m β) (init : γ) {successor_of : β → γ → γ → Prop}
    (f : (b : β) → (c : γ) → n (Subtype fun s : ForInStep γ => successor_of b c s.value)) : n γ := do
  match (← it.stepH).inflate with
  | .yield it' out _ =>
    match ← f out init with
    | ⟨.yield c, _⟩ => IterM.DefaultConsumers.forIn it' c f
    | ⟨.done c, _⟩ => return c
  | .skip it' _ => IterM.DefaultConsumers.forIn it' init f
  | .done _ => return init
termination_by it.finitelyManySteps

class IteratorFor (α : Type w) (m : Type w → Type w') {β : Type v} [Iterator α m β] (n : Type w → Type w'') where
  forIn : ∀ {γ : Type w}, IterM (α := α) m β → γ → {successor_of : β → γ → γ → Prop} →
      ((b : β) → (c : γ) → n (Subtype fun s : ForInStep γ => successor_of b c s.value)) →
      n γ

class LawfulIteratorFor (α : Type w) (m : Type w → Type w') (n : Type w → Type w'')
    [Monad n] [Iterator α m β] [Finite α m] [IteratorFor α m n] [MonadLiftT m n] where
  lawful : ∀ γ, IteratorFor.forIn (α := α) (m := m) (n := n) (γ := γ) =
    IterM.DefaultConsumers.forIn (α := α) (m := m) (n := n) (γ := γ)

def IteratorFor.defaultImplementation {α : Type w} {m : Type w → Type w'} {n : Type w → Type w'}
    [Monad m] [Monad n] [MonadLiftT m n] [Iterator α m β] [Finite α m] :
    IteratorFor α m n where
  forIn := IterM.DefaultConsumers.forIn

instance (α : Type w) (m : Type w → Type w') (n : Type w → Type w')
    [Monad m] [Monad n] [MonadLiftT m n] [Iterator α m β] [Finite α m] :
    haveI : IteratorFor α m n := .defaultImplementation
    LawfulIteratorFor α m n :=
  letI : IteratorFor α m n := .defaultImplementation
  ⟨fun _ => rfl⟩

instance {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type v} [Iterator α m β] [Finite α m] [IteratorFor α m n] :
    ForIn n (IterM (α := α) m β) β where
  forIn it init stepper := IteratorFor.forIn it init
      (successor_of := fun _ _ _ => True)
      (fun b c => (⟨·, True.intro⟩) <$> stepper b c)

@[specialize]
def IterM.foldM {m : Type w → Type w'} {n : Type w → Type w'} [Monad n]
    {α : Type w} {β : Type v} {γ : Type w} [Iterator α m β] [Finite α m] [IteratorFor α m n]
    (f : γ → β → n γ) (init : γ) (it : IterM (α := α) m β) : n γ :=
  ForIn.forIn it init (fun x acc => ForInStep.yield <$> f acc x)

@[specialize]
def IterM.count {α : Type u} {β : Type v} [Iterator α Id β] [Finite α Id]
    (it : IterM (α := α) Id β) : Nat :=
  go it 0
where
  go [Finite α Id] it acc :=
    match it.stepH.inflate with
    | .yield it' _ _ => go it' (acc + 1)
    | .skip it' _ => go it' acc
    | .done _ => acc
  termination_by it.finitelyManySteps

@[specialize]
def IterM.countM {m : Type → Type w'} [Monad m] {α : Type} {β : Type v} [Iterator α m β] [Finite α m]
    (it : IterM (α := α) m β) : m Nat :=
  go it 0
where
  go [Finite α m] it acc := do
    match (← it.stepH).inflate with
      | .yield it' _ _ => go it' (acc + 1)
      | .skip it' _ => go it' acc
      | .done _ => return acc
  termination_by it.finitelyManySteps

@[specialize]
def IterM.drain {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type v}
    [Iterator α m β] [Finite α m] (it : IterM (α := α) m β) [IteratorFor α m m] :
    m PUnit :=
  it.foldM (γ := PUnit) (fun _ _ => pure .unit) .unit
