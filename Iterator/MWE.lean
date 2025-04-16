import Iterator.Generators
import Iterator.Combinators.Take
import Iterator.Combinators.FilterMap
import Iterator.Combinators.FlatMap

set_option trace.compiler.ir.result true in
set_option compiler.small 2 in
def test (l : List Nat) : Nat :=
  go (l.iter Id |>.map (· * 2) |>.take 5) 0
where
  go it acc :=
    match it.step with
    | .yield it' x _ => go it' (acc + x)
    | .skip it' _ => go it' acc
    | .done _ => acc
  termination_by it.terminationByFinite

set_option pp.universes true in
set_option pp.explicit true in
def firstOfEach {α} (l : List (List α)) :=
  let it := List.iter l Id |>.flatMapS (List.iter · Id)
  go (it) 0
where
  go it acc : Nat :=
    match it.step with
    | .yield it' x _ => sorry --go it' acc --(acc + x)
    | .skip it' _ => sorry--go it' acc
    | .done _ => acc
  termination_by it-- .terminationByFinite
  decreasing_by all_goals sorry

set_option trace.compiler.ir.result true in
set_option compiler.small 2 in
def test2 (l : List Nat) : Nat :=
  go (l.iter Id |>.map (· * 2) |>.take 5) 0
where
  go it acc :=
    match it.step with
    | .yield it' x _ => go it' (acc + x)
    | .skip it' _ => go it' acc
    | .done _ => acc
  termination_by it.terminationByFinite
