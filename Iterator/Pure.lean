prelude
import Iterator.Basic

structure Iter {α : Type w} (β : Type v) : Type w where
  inner : α

def Iter.toIterM {α : Type w} {β : Type w} (it : Iter (α := α) β) : IterM (α := α) Id β :=
  ⟨it.inner⟩

def IterM.toPureIter {α : Type w} {β : Type w} (it : IterM (α := α) Id β) : Iter (α := α) β :=
  ⟨it.inner⟩

@[simp]
theorem Iter.toPureIter_toIterM {α : Type w} {β : Type w} (it : Iter (α := α) β) :
    it.toIterM.toPureIter = it :=
  rfl

@[simp]
theorem Iter.toIterM_toPureIter {α : Type w} {β : Type w} (it : IterM (α := α) Id β) :
    it.toPureIter.toIterM = it :=
  rfl

def Iter.plausible_step {α : Type w} {β : Type w} [Iterator α Id β]
    (it : Iter (α := α) β) (step : IterStep (Iter (α := α) β) β) : Prop :=
  it.toIterM.plausible_step (step.map Iter.toIterM id)

def Iter.Step {α : Type w} {β : Type w} [Iterator α Id β] (it : Iter (α := α) β) :=
  PlausibleIterStep (Iter.plausible_step it)

def Iter.plausible_output {α : Type w} {β : Type w} [Iterator α Id β]
    (it : Iter (α := α) β) (out : β) : Prop :=
  ∃ it', it.plausible_step (.yield it' out)

def Iter.plausible_successor_of {α : Type w} {β : Type w} [Iterator α Id β]
    (it' it : Iter (α := α) β) : Prop :=
  ∃ step, step.successor = some it' ∧ it.plausible_step step

def Iter.plausible_skip_successor_of {α : Type w} {β : Type w} [Iterator α Id β]
    (it' it : Iter (α := α) β) : Prop :=
  it.plausible_step (.skip it')

@[always_inline, inline]
def Iter.step {α : Type w} {β : Type w} [Iterator α Id β]
    (it : Iter (α := α) β) : it.Step := by
  refine it.toIterM.step.run.map IterM.toPureIter id _ ?_
  intro step hp
  simp only [Iter.plausible_step, IterStep.map_map, id_eq, IterStep.map_id', toIterM_toPureIter, hp]

section Finite

def Iter.finitelyManySteps {α : Type w} {β : Type w} [Iterator α Id β] [Finite α Id]
    (it : Iter (α := α) β) : IterM.TerminationMeasures.Finite α Id :=
  it.toIterM.finitelyManySteps

theorem Iter.TerminationMeasures.Finite.rel_of_yield
    {α : Type w} {β : Type w} [Iterator α Id β]
    {it it' : Iter (α := α) β} {out : β} (h : it.plausible_step (.yield it' out)) :
    IterM.TerminationMeasures.Finite.rel ⟨it'.toIterM⟩ ⟨it.toIterM⟩ :=
  IterM.TerminationMeasures.Finite.rel_of_yield h

theorem Iter.TerminationMeasures.Finite.rel_of_skip
    {α : Type w} {β : Type w} [Iterator α Id β]
    {it it' : Iter (α := α) β} (h : it.plausible_step (.skip it')) :
    IterM.TerminationMeasures.Finite.rel ⟨it'.toIterM⟩ ⟨it.toIterM⟩ :=
  IterM.TerminationMeasures.Finite.rel_of_skip h

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
  | exact Iter.TerminationMeasures.Finite.rel_of_yield ‹_›
  | exact Iter.TerminationMeasures.Finite.rel_of_skip ‹_›)

end Finite

section Productive

def Iter.finitelyManySkips {α : Type w} {β : Type w} [Iterator α Id β] [Productive α Id]
    (it : Iter (α := α) β) : IterM.TerminationMeasures.Productive α Id :=
  it.toIterM.finitelyManySkips

theorem Iter.TerminationMeasures.Productive.rel_of_skip
    {α : Type w} {β : Type w} [Iterator α Id β]
    {it it' : Iter (α := α) β} (h : it.plausible_step (.skip it')) :
    IterM.TerminationMeasures.Productive.rel ⟨it'.toIterM⟩ ⟨it.toIterM⟩ :=
  IterM.TerminationMeasures.Productive.rel_of_skip h

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  exact Iter.TerminationMeasures.Productive.rel_of_skip ‹_›)

end Productive
