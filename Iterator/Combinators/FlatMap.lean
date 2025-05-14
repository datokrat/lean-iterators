prelude
import Iterator.Combinators.Monadic.FlatMap
import Iterator.Pure

@[always_inline, inline]
def Iter.flatMap {α : Type w} {β : Type w} {α₂ : Type w} {γ : Type w}
    [Iterator α Id β] [Iterator α₂ Id γ] (f : β → Iter (α := α₂) γ)
    (it : Iter (α := α) β) :=
  ((it.toIterM.flatMap (Iter.toIterM ∘ f)).toPureIter : Iter γ)


@[always_inline, inline]
def Iter.flatMapD {α : Type w} {β : Type w} {α₂ : β → Type w} {γ : Type w}
    [Iterator α Id β] [∀ b, Iterator (α₂ b) Id γ] (f : (b : β) → Iter (α := α₂ b) γ)
    (it : Iter (α := α) β) :=
  -- TODO: confusing error message when writing (toIterM ∘ (f b)) (it's fine that it fails)
  ((it.toIterM.flatMapD (fun b => (f b).toIterM)).toPureIter : Iter γ)
