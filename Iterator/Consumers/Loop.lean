import Iterator.Basic

@[specialize]
def IterM.DefaultConsumers.forIn {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n] (lift : ∀ γ, m γ → n γ)
    {α : Type w} {β : Type v} {γ : Type w}
    [Iterator α m β] [Finite α m]
    (it : IterM (α := α) m β) (init : γ)
    (f : (b : β) → (c : γ) → n (ForInStep γ)) : n γ :=
  letI : MonadLift m n := ⟨fun {γ} => lift γ⟩
  do
    match (← it.stepH).inflate with
    | .yield it' out _ =>
      match ← f out init with
      | .yield c => IterM.DefaultConsumers.forIn lift it' c f
      | .done c => return c
    | .skip it' _ => IterM.DefaultConsumers.forIn lift it' init f
    | .done _ => return init
termination_by it.finitelyManySteps

class IteratorFor (α : Type w) (m : Type w → Type w') {β : Type v} [Iterator α m β]
    (n : Type w → Type w'') where
  forIn : ∀ (_lift : (γ : Type w) → m γ → n γ) {γ : Type w},
      IterM (α := α) m β → γ →
      ((b : β) → (c : γ) → n (ForInStep γ)) → n γ

class LawfulIteratorFor (α : Type w) (m : Type w → Type w') (n : Type w → Type w'')
    [Monad n] [Iterator α m β] [Finite α m] [IteratorFor α m n] where
  lawful : ∀ lift γ, IteratorFor.forIn lift (α := α) (m := m) (γ := γ) =
    IterM.DefaultConsumers.forIn (α := α) (m := m) (n := n) (lift := lift) (γ := γ)

def IteratorFor.defaultImplementation {α : Type w} {m : Type w → Type w'} {n : Type w → Type w'}
    [Monad m] [Monad n] [Iterator α m β] [Finite α m] :
    IteratorFor α m n where
  forIn lift := IterM.DefaultConsumers.forIn lift

instance (α : Type w) (m : Type w → Type w') (n : Type w → Type w')
    [Monad m] [Monad n] [Iterator α m β] [Finite α m] :
    letI : IteratorFor α m n := .defaultImplementation
    LawfulIteratorFor α m n :=
  letI : IteratorFor α m n := .defaultImplementation
  ⟨fun _ _ => rfl⟩

instance {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type v} [Iterator α m β] [IteratorFor α m n]
    [MonadLiftT m n] :
    ForIn n (IterM (α := α) m β) β where
  forIn := IteratorFor.forIn (fun _ => MonadLiftT.monadLift)

@[specialize]
def IterM.foldM {m : Type w → Type w'} {n : Type w → Type w'} [Monad n]
    {α : Type w} {β : Type v} {γ : Type w} [Iterator α m β] [IteratorFor α m n]
    [MonadLiftT m n]
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
