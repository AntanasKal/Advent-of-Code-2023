import Std.Data.RBMap
import Std.Data.RBMap.Basic
-- #eval Std.RBMap.empty

def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  if not (← filename.pathExists) then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File '{filename.toString}' cannot be found"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))

partial def getLinesHelper (stream : IO.FS.Stream) (currentList : List String) : IO (List String) := do
  let line ← stream.getLine
  if line.length == 0 then
    pure currentList
  else
    (getLinesHelper stream (line.dropRight 1 :: currentList))

def getLines (path : String) : IO (List String) := do
  let optionStream ← fileStream (System.FilePath.mk path)
  match optionStream with
  | none =>
    IO.println "Failed to construct a filestream"
    pure []
  | some stream =>
    getLinesHelper stream []

def getNumbers (str : String) : Option (List Int) :=
  str.splitOn (" ") |> List.mapM String.toInt?

#eval String.toInt? "-3"
#eval (-5) +(-2)

def getDifferences : List Int → List Int
  | (x1::x2::xs) => (x2-x1)::(getDifferences (x2::xs))
  | [_] | [] => []


-- TODO: complete this
theorem getDifferencesDecreases (list : List Int) : (list.length > 0) → (getDifferences list).length < list.length := by
  sorry
  -- induction list with
  -- | nil => intro h; simp; contradiction
  -- | cons h tail ih =>
  --   cases tail with
  --   | nil => simp[getDifferences]
  --   | cons x nil =>
  --     have h1 : List.length (x :: nil) > 0 := by simp[List.length, Nat.zero_lt_succ]
  --     have h2 : List.length (getDifferences (x :: nil)) < List.length (x :: nil) := by exact (ih h)
  --     intros; simp[getDifferences, ih]; apply Nat.succ_lt_succ; simp

#eval getDifferences [1, 3, 6, 10, 15, 21]

def repeatedDifferences (numbers : List Int) (soFar : List (List Int)) : List (List Int) :=
  let currentDifferences := getDifferences numbers
  match currentDifferences.all (·==0), currentDifferences with
  | true, _ => currentDifferences::numbers::soFar
  | _, [] => soFar
  | _, x::xs =>
    have : currentDifferences.length < numbers.length := sorry --TODO
    repeatedDifferences (currentDifferences) (numbers::soFar)
  termination_by repeatedDifferences numbs soFar => numbs.length


#eval repeatedDifferences [1, 3, 6, 10, 15, 21] []

def getPrediction (list : List Int) : Option Int :=
  let differences := repeatedDifferences list []
  List.foldlM (fun accum single_diffs =>
    do
      let last ←single_diffs.getLast?
      pure (last + accum)
    ) (0 : Int) differences

#eval getPrediction [1, 3, 6, 10, 15, 21]
#eval getPrediction [10,  13,  16,  21,  30,  45]

#eval getPrediction [0, 3, 6, 9, 12, 15]

def solvePart1Helper (lines : List String) : Option Int := do
  let predictions ← (← lines.mapM getNumbers).mapM getPrediction  -- (getNumbers >>= getPrediction)
  pure $ predictions.foldr (Int.add) (0)


def solvePart2Helper (lines : List String) : Option Int := do
  let predictions ← (← lines.mapM (fun x => (getNumbers x).map List.reverse)).mapM getPrediction  -- (getNumbers >>= getPrediction)
  pure $ predictions.foldr (Int.add) (0)


def solvePart1 (lines : List String) : Int :=
  match solvePart1Helper lines with
  | some x => x
  | none => 0


def solvePart2 (lines : List String) : Int :=
  match solvePart2Helper lines with
  | some x => x
  | none => 0

def main (args : List String) : IO Unit :=
  if inBounds : 1 < args.length then
    do
      have inBounds0 : 0 < args.length := by
        exact Nat.lt_trans (Nat.zero_lt_one) (inBounds)
      match args.get ⟨0, inBounds0⟩ with
      |"part1" =>
        let lines := (←getLines (args.get (Fin.mk 1 inBounds))).reverse
        IO.println (solvePart1 lines)
        -- IO.println (solvePart1Helper' lines)
      | "part2" =>
        let lines := (←getLines (args.get (Fin.mk 1 inBounds))).reverse
        IO.println (solvePart2 lines)

      | _ => IO.println "Wrong argument, should be 'part1' or 'part2'"
  else
    IO.println ("not enough args")
