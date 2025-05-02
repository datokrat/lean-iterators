import Iterator.Basic

class IteratorFor (α : Type w) (m : Type w → Type w') (β : Type v) [Iterator α m β] (n : Type w → Type w'') where
  forIn : ∀ {γ : Type w}, Iter (α := α) m β → γ → (β → γ → n (ForInStep γ)) → n γ

@[specialize]
def Iter.DefaultConsumers.forIn {m : Type w → Type w'} {n : Type w → Type w''} [Monad m] [Monad n] [MonadLiftT m n]
    {α : Type w} {β : Type v} {γ : Type w}
    [Iterator α m β] [Finite α m]
    (it : Iter (α := α) m β) (init : γ) (f : β → γ → n (ForInStep γ)) : n γ := do
  match (← it.stepH).inflate with
  | .yield it' out _ =>
    match ← f out init with
    | .yield c => Iter.DefaultConsumers.forIn it' c f
    | .done c => return c
  | .skip it' _ => Iter.DefaultConsumers.forIn it' init f
  | .done _ => return init
termination_by it.finitelyManySteps

instance {m : Type w → Type w'} {n : Type w → Type w''} [Monad m]
    {α : Type w} {β : Type v} [Iterator α m β] [IteratorFor α m β n] :
    ForIn n (Iter (α := α) m β) β where
  forIn := IteratorFor.forIn

@[specialize]
def Iter.foldM {m : Type w → Type w'} {n : Type w → Type w'} [Monad m] [Functor n]
    {α : Type w} {β : Type v} {γ : Type w} [Iterator α m β] [IteratorFor α m β n]
    (f : γ → β → n γ) (init : γ) (it : Iter (α := α) m β) : n γ :=
  IteratorFor.forIn it init (fun x acc => ForInStep.yield <$> f acc x)

@[specialize]
def Iter.count {α : Type u} {β : Type v} {_ : Iterator α Id β} [Finite α Id] {_ : ComputableSmall.{0} α}
    (it : Iter (α := α) Id β) : Nat :=
  go it 0
where
  go [Finite α Id] it acc :=
    match it.stepH.inflate with
    | .yield it' _ _ => go it' (acc + 1)
    | .skip it' _ => go it' acc
    | .done _ => acc
  termination_by it.finitelyManySteps

@[specialize]
def Iter.countM {m : Type → Type w'} [Monad m] {α : Type} {β : Type v} [Iterator α m β] [Finite α m] {_ : ComputableSmall.{0} α}
    (it : Iter (α := α) m β) : m Nat :=
  go it 0
where
  go [Finite α m] it acc := do
    match (← it.stepH).inflate with
      | .yield it' _ _ => go it' (acc + 1)
      | .skip it' _ => go it' acc
      | .done _ => return acc
  termination_by it.finitelyManySteps

@[specialize]
def Iter.drain {α : Type w} {m : Type w → Type w'} {β : Type v} [Monad m]
    [Iterator α m β] (it : Iter (α := α) m β) [IteratorFor α m β m] :
    m PUnit := do
  it.foldM (γ := PUnit) (fun _ _ => pure .unit) .unit
