import Iterator.Consumers
import Iterator.Combinators.FilterMap
import Iterator.Lemmas.Equivalence
import Iterator.Producers

section Consumers

def Iter.induct {α m β} [Iterator α m β] [Finite α m]
  (motive : Iter (α := α) m β → Sort x)
  (step : (it : Iter (α := α) m β) →
    (ih_yield : ∀ {it' : Iter (α := α) m β} {out : β}, it.plausible_step (.yield it' out) → motive it') →
    (ih_skip : ∀ {it' : Iter (α := α) m β}, it.plausible_step (.skip it') → motive it' ) →
    motive it) (it : Iter (α := α) m β) : motive it :=
  step _ (fun {it' _} _ => Iter.induct motive step it') (fun {it'} _ => Iter.induct motive step it')
termination_by it.finitelyManySteps

theorem Iter.DefaultConsumers.toArrayMapped.go.aux₁ [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : Iter (α := α) m β} {b : γ} {bs : Array γ} {f : β → m γ} :
    Iter.DefaultConsumers.toArrayMapped.go f it (#[b] ++ bs) = (#[b] ++ ·) <$> Iter.DefaultConsumers.toArrayMapped.go f it bs := by
  induction it, bs using Iter.DefaultConsumers.toArrayMapped.go.induct
  next it bs ih₁ ih₂ =>
  rw [go, map_eq_pure_bind, go, bind_assoc]
  refine congrArg (Iter.stepH it >>= ·) ?_
  ext step
  generalize step.inflate = step
  split
  · simp [ih₁ _ _ ‹_›]
  · simp [ih₂ _ ‹_›]
  · simp

theorem Iter.DefaultConsumers.toArrayMapped.go.aux₂ [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] {it : Iter (α := α) m β} {acc : Array γ} {f : β → m γ} :
    Iter.DefaultConsumers.toArrayMapped.go f it acc =
      (acc ++ ·) <$> Iter.DefaultConsumers.toArrayMapped f it := by
  rw [← Array.toArray_toList (xs := acc)]
  generalize acc.toList = acc
  induction acc with
  | nil => simp [toArrayMapped]
  | cons x xs ih =>
    rw [List.toArray_cons, Iter.DefaultConsumers.toArrayMapped.go.aux₁, ih]
    simp only [Functor.map_map, Array.append_assoc]

theorem Iter.DefaultConsumers.toArrayMapped_of_stepH [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] {it : Iter (α := α) m β} {f : β → m γ} :
    Iter.DefaultConsumers.toArrayMapped f it = (do
      match (← it.stepH).inflate with
      | .yield it' out _ => return #[← f out] ++ (← Iter.DefaultConsumers.toArrayMapped f it')
      | .skip it' _ => Iter.DefaultConsumers.toArrayMapped f it'
      | .done _ => return #[]) := by
  rw [Iter.DefaultConsumers.toArrayMapped, Iter.DefaultConsumers.toArrayMapped.go]
  apply bind_congr
  intro step
  generalize step.inflate = step
  split <;> simp [Iter.DefaultConsumers.toArrayMapped.go.aux₂]

theorem Iter.DefaultConsumers.toArrayMapped_of_step [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] {it : Iter (α := α) m β} {f : β → m γ} :
    Iter.DefaultConsumers.toArrayMapped f it = (do
      match ← it.step with
      | .yield it' out _ => return #[← f out] ++ (← Iter.DefaultConsumers.toArrayMapped f it')
      | .skip it' _ => Iter.DefaultConsumers.toArrayMapped f it'
      | .done _ => return #[]) := by
  rw [Iter.DefaultConsumers.toArrayMapped_of_stepH, Iter.step, map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro step
  generalize step.inflate = step
  rw [pure_bind]
  rfl

theorem Iter.toArray_of_step [Monad m] [LawfulMonad m]
    [Iterator α m β] [IteratorToArray α m] [LawfulIteratorToArray α m]
    {it : Iter (α := α) m β} :
    it.toArray = (do
      match ← it.step with
      | .yield it' out _ => return #[out] ++ (← it'.toArray)
      | .skip it' _ => it'.toArray
      | .done _ => return #[]) := by
  rw [Iter.toArray, LawfulIteratorToArray.lawful, Iter.DefaultConsumers.toArrayMapped_of_step]
  simp only [bind_pure_comp, pure_bind, toArray, LawfulIteratorToArray.lawful]

theorem Iter.toList_toArray [Monad m] [Iterator α m β] [IteratorToArray α m]
    {it : Iter (α := α) m β} :
    Array.toList <$> it.toArray = it.toList := by
  simp [Iter.toList]

theorem Iter.toArray_toList [Monad m] [LawfulMonad m] [Iterator α m β] [IteratorToArray α m]
    {it : Iter (α := α) m β} :
    List.toArray <$> it.toList = it.toArray := by
  simp [Iter.toList]

theorem Iter.toList_of_step [Monad m] [LawfulMonad m] [Iterator α m β]
    [IteratorToArray α m] [LawfulIteratorToArray α m] {it : Iter (α := α) m β} :
    it.toList = (do
      match ← it.step with
      | .yield it' out _ => return out :: (← it'.toList)
      | .skip it' _ => it'.toList
      | .done _ => return []) := by
  simp [← Iter.toList_toArray]
  rw [Iter.toArray_of_step, map_eq_pure_bind, bind_assoc]
  refine congrArg (_ >>= ·) ?_
  ext step
  split <;> simp

theorem Iter.reverseToList.go.aux₁ [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : Iter (α := α) m β} {b : β} {bs : List β} :
    Iter.reverseToList.go it (bs ++ [b]) = (· ++ [b]) <$> Iter.reverseToList.go it bs:= by
  induction it, bs using Iter.reverseToList.go.induct
  next it bs ih₁ ih₂ =>
  rw [go, go, map_eq_pure_bind, bind_assoc]
  refine congrArg (Iter.step it >>= ·) ?_
  ext step
  simp only [List.cons_append] at ih₁
  split <;> simp [*]

theorem Iter.reverseToList.go.aux₂ [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : Iter (α := α) m β} {acc : List β} :
    Iter.reverseToList.go it acc = (· ++ acc) <$> it.reverseToList := by
  rw [← List.reverse_reverse (as := acc)]
  generalize acc.reverse = acc
  induction acc with
  | nil => simp [reverseToList]
  | cons x xs ih => simp [Iter.reverseToList.go.aux₁, ih]

theorem Iter.reverseToList_of_step [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : Iter (α := α) m β} :
    it.reverseToList = (do
      match ← it.step with
      | .yield it' out _ => return (← it'.reverseToList) ++ [out]
      | .skip it' _ => it'.reverseToList
      | .done _ => return []) := by
  simp [Iter.reverseToList]
  rw [reverseToList.go]
  refine congrArg (it.step >>= ·) ?_
  ext step
  obtain ⟨step, h⟩ := step
  cases step <;> simp [Iter.reverseToList.go.aux₂]

-- TODO: rename `reverseToList` -> `toListRev`
theorem Iter.reverse_reverseToList [Monad m] [LawfulMonad m] [Iterator α m β]
    [IteratorToArray α m] [LawfulIteratorToArray α m]
    {it : Iter (α := α) m β} :
    List.reverse <$> it.reverseToList = it.toList := by
  apply Eq.symm
  induction it using Iter.induct
  rename_i it ihy ihs
  rw [reverseToList_of_step, toList_of_step, map_eq_pure_bind, bind_assoc]
  refine congrArg (_ >>= ·) ?_
  ext step
  split <;> simp (discharger := assumption) [ihy, ihs]

end Consumers

section Congruence

theorem Iter.Morphism.toArrayMapped_eq {α α' : Type w} {m : Type w → Type w'}
    {β : Type v} {γ : Type w}
    [Monad m] [LawfulMonad m]
    [Iterator α m β] [Iterator α' m β] [IteratorToArray α m] [LawfulIteratorToArray α m]
    [IteratorToArray α' m] [LawfulIteratorToArray α' m]
    (φ : Morphism α α' m) {f : β → m γ} {it : Iter (α := α) m β} :
    IteratorToArray.toArrayMapped f it = IteratorToArray.toArrayMapped f (φ.map it) := by
  haveI : Finite α m := LawfulIteratorToArray.finite
  haveI : Finite α' m := LawfulIteratorToArray.finite
  simp only [LawfulIteratorToArray.lawful]
  induction it using Iter.induct with | step it ihy ihs =>
  rw [DefaultConsumers.toArrayMapped_of_stepH, DefaultConsumers.toArrayMapped_of_stepH]
  simp only [← φ.stepH_hom, map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro step
  generalize step.inflate = step
  obtain ⟨step, _⟩ := step
  cases step <;> simp (discharger := assumption) [PlausibilityMorphism.mapStep, IterStep.map, ihs, ihy]

theorem Iter.Morphism.toArray_eq {α α' : Type w} {m : Type w → Type w'} {β : Type w}
    [Monad m] [LawfulMonad m]
    [Iterator α m β] [Iterator α' m β] [IteratorToArray α m] [LawfulIteratorToArray α m]
    [IteratorToArray α' m] [LawfulIteratorToArray α' m]
    (φ : Morphism α α' m) {it : Iter (α := α) m β} :
    it.toArray = (φ.map it).toArray := by
  simp [Iter.toArray, φ.toArrayMapped_eq]

theorem Iter.Morphism.toList_eq {α α' : Type w} {m : Type w → Type w'} {β : Type w}
    [Monad m] [LawfulMonad m]
    [Iterator α m β] [Iterator α' m β] [IteratorToArray α m] [LawfulIteratorToArray α m]
    [IteratorToArray α' m] [LawfulIteratorToArray α' m]
    (φ : Morphism α α' m) {it : Iter (α := α) m β} :
    it.toList = (φ.map it).toList := by
  simp [← Iter.toList_toArray, φ.toArray_eq]

end Congruence
