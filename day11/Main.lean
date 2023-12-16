-- import Std.Data.RBMap
-- import Std.Data.RBMap.Basic
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


def galaxiesInLine (line : String) : List Nat :=
  line.toList |> List.zip (List.range line.toList.length)
  |> List.filter (·.snd == '#') |> List.map (·.fst)

def getGalaxies (lines : List String) : List (Nat × Nat) :=
  lines.zip (List.range lines.length) |> List.map (fun (line,y) => (galaxiesInLine line).map (fun x => (x,y)))
  |> List.join

def getEmptyRows (galaxies : List (Nat × Nat)) (xMax : Nat) (yMax : Nat) : List Nat :=
  List.range yMax |> List.filter (fun y => (galaxies.all (·.snd != y)))
def getEmptyColumns (galaxies : List (Nat × Nat)) (xMax : Nat) (yMax : Nat) : List Nat :=
  List.range xMax |> List.filter (fun x => (galaxies.all (·.fst != x)))

def getDistance1Dim (expansionFactor : Nat) (p1 p2 : Nat) (emptySpace : List Nat) : Nat :=
  let xMin := Nat.min p1 p2
  let xMax := Nat.max p1 p2
  let emptyColNum := emptySpace.filter (fun x => x<xMax && x>xMin) |> List.length
  (xMax - xMin) +(emptyColNum*(expansionFactor-1))

def getDistance (expansionFactor : Nat) (emptyRows emptyColumns : List Nat) (p1 p2 : Nat × Nat) : Nat :=
  (getDistance1Dim expansionFactor p1.fst p2.fst emptyColumns) + (getDistance1Dim expansionFactor p1.snd p2.snd emptyRows)

def getUniquePairs (points : List (Nat × Nat)) : List ((Nat×Nat) × (Nat × Nat)) :=
  match points with
  | [] => []
  | x::xs => xs.map (fun p => (x,p)) ++ (getUniquePairs xs)

-- #eval getDistance/

def solveHelper (lines : List String) (expansionFactor : Nat): Option Nat := do
  -- some 5
  let galaxies := getGalaxies lines
  let xMax := (← lines.get? 0).toList.length
  let yMax := lines.length
  let emptyRows := getEmptyRows galaxies xMax yMax
  let emptyColumns := getEmptyColumns galaxies xMax yMax
  let distances := getUniquePairs galaxies |> List.map (fun (p1, p2) => getDistance expansionFactor emptyRows emptyColumns p1 p2)
  some (distances.foldr (Nat.add) 0)

def solvePart2Helper (lines : List String) : Option Nat := do
  some 0



def solvePart1 (lines : List String) : Nat :=
  match solveHelper lines 2 with
  | some x => x
  | none => 0


def solvePart2 (lines : List String) : Nat :=
  match solveHelper lines 1000000 with
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
      | "part2" =>
        let lines := (←getLines (args.get (Fin.mk 1 inBounds))).reverse
        IO.println (solvePart2 lines)

      | _ => IO.println "Wrong argument, should be 'part1' or 'part2'"
  else
    IO.println ("not enough args")
