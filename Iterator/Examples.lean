import Iterator
import Std.Time

def firstOfEach (l : List (List Nat)) : List Nat :=
  l.iter.flatMap (·.iter.take 1) |>.toList

/-- info: [1, 3] -/
#guard_msgs in
#eval firstOfEach [[1, 2], [], [3, 4]]

def staggeredCounting : List Nat :=
  Iter.unfold Id 0 (· + 1) |>.take 5 |>.flatMap
    (fun i => Iter.unfold Id 0 (· + 1) |>.take i) |>.toList

/-- info: [0, 0, 1, 0, 1, 2, 0, 1, 2, 3] -/
#guard_msgs in
#eval staggeredCounting

-- The error message is not the nicest but at least we get an error as expected.
-- Underlying problem: The inner iterators of the flatMap operation don't terminate!
/--
error: failed to synthesize
  Finite
    (Flatten
      (FilterMapMH (Take (UnfoldIterator Nat (fun x => x + 1) Id))
        (fun b =>
          pure
            {
              down :=
                (fun b => some (IterULiftState.up (Iter.unfold 0 (fun x => x + 1) Id) fun ⦃x x_1⦄ => Functor.map)) b })
        fun ⦃x x_1⦄ => Functor.map))
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
-- #guard_msgs in
-- def notTerminating : List Nat :=
--   Iter.unfold Id 0 (· + 1) |>.take 5 |>.flatMap
--     (fun i => Iter.unfold Id 0 (fun x => x + 1)) |>.toList

-- The following works -- but don't uncomment it except you want to heat your room for 15s with the compiler:
-- But it's nice that it works since such dependent flat map operations require boxing in non-dependent languages such
-- as Rust

def dependentFlatMap (l : List (List Nat)) : List Nat :=
  let it := Iter.unfold Id 2 (· + 1) |>.zip l.iter -- It's not nice that this fails if we don't provide Id explicitly.
  -- the ⟨_, ⟩ is a hack to provide the correct ComputableSmall instance
  it.flatMapD (fun (x : Nat × List Nat) => ⟨_, (x.2.iter Id).filter fun y => y % x.1 = 0⟩) |>.toList

/-- info: [2, 6, 9] -/
#guard_msgs in
#eval dependentFlatMap [[1, 2, 3], [4, 5, 6, 9]]

def addIndices (l : List Nat) : List (Nat × Nat) :=
  Iter.unfold Id 0 (· + 1) |>.zip (l.iter Id) |>.toList

/-- info: [(0, 3), (1, 1), (2, 4), (3, 1), (4, 5), (5, 9)] -/
#guard_msgs in
#eval addIndices [3, 1, 4, 1, 5, 9]

/-- info: [4] -/
#guard_msgs in
#eval [3, 1, 4, 1, 5, 9].iter.filter (· % 2 = 0) |>.toList

def printNums (l : List Nat) : IO Unit :=
  l.iter IO |>.mapM (fun n => do IO.println (toString n); pure n) |>.drain


/--
info: 1
2
3
-/
#guard_msgs in
#eval printNums [1, 2, 3]

-- Same result as `printNums` but showcasing that we can use iterators in `for-in` constructs
def printNumsForIn (l : List Nat) : IO Unit := do
  for n in l.iter IO do
    IO.println n

def timestamps (n : Nat) : IO (List Std.Time.PlainTime) := do
  Iter.unfold IO 0 (fun _ => 0) |>.take n |>.mapM (fun _ => Std.Time.PlainTime.now) |>.toList

/-
info: [time("13:47:35.833520000"),
 time("13:47:35.833670000"),
 time("13:47:35.833722000"),
 time("13:47:35.833774000"),
 time("13:47:35.833820000")]
-/
-- #eval timestamps 5

-- Note: The following wouldn't work because the `Productive` instance for `.mapM` is still missing
/-
def timestamps (n : Nat) : IO (List Std.Time.PlainTime) := do
  Iter.unfold 0 (fun _ => 0) IO |>.take n |>.mapM (fun _ => Std.Time.PlainTime.now) |>.toList
-/

-- This example demonstrates that chained `mapM` calls are executed in a different order than with `List.mapM`.
def chainedMapM (l : List Nat) : IO Unit :=
  l.iter IO |>.mapM (IO.println <| s!"1st {.}") |>.mapM (IO.println <| s!"2nd {·}") |>.drain

/--
info: 1st 1
2nd ()
1st 2
2nd ()
1st 3
2nd ()
-/
#guard_msgs in
#eval chainedMapM [1, 2, 3]
