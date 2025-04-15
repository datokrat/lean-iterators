import Iterator.Generators
import Iterator.Combinators.Take

set_option trace.compiler.ir.result true in
set_option compiler.small 2 in
def test (l : List Nat) : Nat :=
  go (l.iter Id |>.take 5) 0
where
  go it acc :=
    match it.step with
    | .yield it' x _ => go it' (acc + x)
    | .skip it' _ => go it' acc
    | .done _ => acc
  termination_by it.terminationByFinite
