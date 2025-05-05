import Iterator.Basic

def Iter.ForInWillTerminate (α : Type w) (m : Type w → Type w') {β : Type v} [Iterator α m β] {γ : Type w}
    (successor_of : β → γ → γ → Prop) : Prop :=
  WellFounded (fun (c' c : Iter (α := α) m β × γ) =>
    (c'.1.plausible_skip_successor_of c.1 ∧ c'.2 = c.2) ∨ (∃ b, c.1.plausible_step (.yield c'.1 b) ∧ successor_of b c.2 c'.2))

def Iter.TerminationMeasures.ForInTerminates {α : Type w} {m : Type w → Type w'} {β : Type v} [Iterator α m β] {γ : Type w}
    {successor_of : β → γ → γ → Prop} (_terminates : Iter.ForInWillTerminate α m successor_of) := Iter (α := α) m β × γ

def Iter.TerminationMeasures.ForInTerminates.mk {α : Type w} {m : Type w → Type w'} {β : Type v} [Iterator α m β] {γ : Type w}
    {successor_of : β → γ → γ → Prop} (terminates : Iter.ForInWillTerminate α m successor_of) (it : Iter (α := α) m β) (c : γ) :
    ForInTerminates terminates :=
  (it, c)

instance {α : Type w} {m : Type w → Type w'} {β : Type v} [Iterator α m β] {γ : Type w}
    {successor_of : β → γ → γ → Prop} {terminates : Iter.ForInWillTerminate α m successor_of} :
    WellFoundedRelation (Iter.TerminationMeasures.ForInTerminates terminates) where
  rel p' p := (p'.1.plausible_skip_successor_of p.1 ∧ p'.2 = p.2) ∨ (∃ b, p.1.plausible_step (.yield p'.1 b) ∧ successor_of b p.2 p'.2)
  wf := terminates

@[specialize]
def Iter.DefaultConsumers.forIn {m : Type w → Type w'} {n : Type w → Type w''} [Monad n] [MonadLiftT m n]
    {α : Type w} {β : Type v} {γ : Type w}
    [Iterator α m β]
    (it : Iter (α := α) m β) (init : γ) {successor_of : β → γ → γ → Prop}
    (f : (b : β) → (c : γ) → n (Subtype fun s : ForInStep γ => successor_of b c s.value))
    (terminates : Iter.ForInWillTerminate α m successor_of) : n γ := do
  match (← it.stepH).inflate with
  | .yield it' out _ =>
    match ← f out init with
    | ⟨.yield c, _⟩ => Iter.DefaultConsumers.forIn it' c f terminates
    | ⟨.done c, _⟩ => return c
  | .skip it' _ => Iter.DefaultConsumers.forIn it' init f terminates
  | .done _ => return init
termination_by Iter.TerminationMeasures.ForInTerminates.mk terminates it init
decreasing_by
  · apply Or.inr
    exact ⟨out, ‹_›, ‹_›⟩
  · apply Or.inl
    exact ⟨‹_›, rfl⟩

class IteratorFor (α : Type w) (m : Type w → Type w') {β : Type v} [Iterator α m β] (n : Type w → Type w'') where
  forIn : ∀ {γ : Type w}, Iter (α := α) m β → γ → {successor_of : β → γ → γ → Prop} →
      ((b : β) → (c : γ) → n (Subtype fun s : ForInStep γ => successor_of b c s.value)) →
      (Iter.ForInWillTerminate α m successor_of) → n γ

class LawfulIteratorFor (α : Type w) (m : Type w → Type w') (n : Type w → Type w'')
    [Monad n] [Iterator α m β] [IteratorFor α m n] [MonadLiftT m n] where
  lawful : ∀ γ, IteratorFor.forIn (α := α) (m := m) (n := n) (γ := γ) =
    Iter.DefaultConsumers.forIn (α := α) (m := m) (n := n) (γ := γ)

def IteratorFor.defaultImplementation {α : Type w} {m : Type w → Type w'} {n : Type w → Type w'}
    [Monad m] [Monad n] [MonadLiftT m n] [Iterator α m β] : IteratorFor α m n where
  forIn := Iter.DefaultConsumers.forIn

instance (α : Type w) (m : Type w → Type w') (n : Type w → Type w')
    [Monad m] [Monad n] [MonadLiftT m n] [Iterator α m β] :
    haveI : IteratorFor α m n := .defaultImplementation
    LawfulIteratorFor α m n :=
  letI : IteratorFor α m n := .defaultImplementation
  ⟨fun _ => rfl⟩

instance {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type v} [Iterator α m β] [Finite α m] [IteratorFor α m n] :
    ForIn n (Iter (α := α) m β) β where
  forIn it init stepper := by
    apply IteratorFor.forIn it init (successor_of := fun _ _ _ => True) (fun b c => (⟨·, True.intro⟩) <$> stepper b c)
    simp only [Iter.ForInWillTerminate]
    refine Subrelation.wf (r := InvImage Iter.TerminationMeasures.Finite.rel (fun p => p.1.finitelyManySteps)) ?_ ?_
    · intro p' p h
      cases h
      · apply Iter.TerminationMeasures.Finite.rel_of_skip
        rename_i h
        exact h.1
      · rename_i h
        obtain ⟨out, h, _⟩ := h -- Interesting: Moving `obtain` after `apply` leads to failure
        apply Iter.TerminationMeasures.Finite.rel_of_yield
        exact h
    · apply InvImage.wf
      exact WellFoundedRelation.wf

@[specialize]
def Iter.foldM {m : Type w → Type w'} {n : Type w → Type w'} [Monad n]
    {α : Type w} {β : Type v} {γ : Type w} [Iterator α m β] [Finite α m] [IteratorFor α m n]
    (f : γ → β → n γ) (init : γ) (it : Iter (α := α) m β) : n γ :=
  ForIn.forIn it init (fun x acc => ForInStep.yield <$> f acc x)

@[specialize]
def Iter.count {α : Type u} {β : Type v} [Iterator α Id β] [Finite α Id]
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
def Iter.countM {m : Type → Type w'} [Monad m] {α : Type} {β : Type v} [Iterator α m β] [Finite α m]
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
def Iter.drain {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type v}
    [Iterator α m β] [Finite α m] (it : Iter (α := α) m β) [IteratorFor α m m] :
    m PUnit :=
  it.foldM (γ := PUnit) (fun _ _ => pure .unit) .unit
