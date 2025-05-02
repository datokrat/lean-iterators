import Iterator.Basic

class IteratorSized (α : Type u) (m : Type w → Type w') where
  size : α → Option Nat
