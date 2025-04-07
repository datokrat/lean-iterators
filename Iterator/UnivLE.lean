prelude

class UnivLE.{u, v} where
  lift : Type u → Type v
  up : {α : Type u} → α → lift α
  down : {α : Type u} → lift α → α
