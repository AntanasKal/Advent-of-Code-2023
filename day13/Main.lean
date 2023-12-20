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

inductive Tile
  | Ash
  | Rock
  deriving Repr, BEq

def List.splitHelper (list : List α) (soFar : List α) (p : α → Bool) : List (List α) :=
  match list, soFar with
  | [], [] => []
  | [], y::ys => [(y::ys).reverse]
  | x::xs, [] => if not (p x) then List.splitHelper xs [x] p else List.splitHelper xs [] p
  | x::xs, y::ys => if not (p x) then List.splitHelper xs (x::y::ys) p else (y::ys).reverse::(List.splitHelper xs [] p)

#eval List.splitHelper [1, 4, 5, 2, 3, 5, 2, 4, 2] [] (·==2)

def List.split (list : List α) (p : α → Bool) : List (List α) := List.splitHelper list [] p

def linesToSegments (lines : List String) : List (List String) :=
  lines.split (String.length · == 0)

def parseLine (line : String) : Option (List Tile) :=
  line.toList.mapM (fun c =>
    match c with
    | '.' => some Tile.Ash
    | '#' => some Tile.Rock
    | _ => none
  )

def parsePattern (lines : List String) : Option (List (List Tile)) :=
  lines.mapM parseLine

def mirroredVertically (pattern : List (List Tile)) (colNum : Nat) : Bool :=
  if colNum == 0
    || pattern.any (fun row => row.length <= colNum)
    || pattern.length == 0
    || pattern.any (·.length == 0)  then
    False
  else
    pattern.all (fun row =>
      let left_side := row.take colNum
      let right_side := row.drop colNum
      let min_length := min left_side.length right_side.length
      left_side.drop (left_side.length - min_length) == right_side.reverse.drop (right_side.length - min_length))

def mirroredHorizontally (pattern : List (List Tile)) (rowNum : Nat) : Bool :=
  if rowNum == 0 || rowNum >= pattern.length then
    False
  else
    let upper := pattern.take rowNum
    let lower := pattern.drop rowNum
    let min_length := min upper.length lower.length
    (upper.drop (upper.length - min_length)) == (lower.reverse.drop (lower.length - min_length))

-- #eval Seq

#eval mirroredVertically [[Tile.Ash, Tile.Rock, Tile.Rock]] 1

def somePattern :=   [ [Tile.Rock, Tile.Rock],
    [Tile.Rock, Tile.Ash],
    [Tile.Rock, Tile.Ash],
    [Tile.Rock, Tile.Rock]
    ]

#eval parsePattern ["##", "#.", "#.", "##", "..", ".."]

#eval   parsePattern ["##", "#.", "#.", "##"] == somePattern
#eval (List.range 10).find? (mirroredHorizontally somePattern)

def getReflectionNumber (pattern : List (List Tile)) : Option Nat := do
  let row_num := pattern.length
  let col_num := (←pattern.get? 0).length
  let horizontalNumbers := (List.range row_num).filter (mirroredHorizontally pattern) |> List.map (fun x => 100*x)
  let verticalNumbers := (List.range col_num).filter (mirroredVertically pattern)
  (horizontalNumbers++verticalNumbers).get? 0

def getReflectionNumber' (pattern : List (List Tile)) (previousNumber : Nat) : Option Nat := do
  let row_num := pattern.length
  let col_num := (←pattern.get? 0).length
  let horizontalNumbers := (List.range row_num).filter (mirroredHorizontally pattern) |> List.map (fun x => 100*x)
  let verticalNumbers := (List.range col_num).filter (mirroredVertically pattern)

  match (horizontalNumbers++verticalNumbers).filter (·!= previousNumber) with
    | [] => none
    | x::xs => some x

def swapAt (pattern : List (List Tile)) (c r : Nat) : List (List Tile) :=
  match pattern.get? r with
  | some row =>
    match row.get? c with
    | some col =>
      pattern.set r (List.set row c (if col == Tile.Ash then Tile.Rock else Tile.Ash))
    | none => pattern
  | none => pattern

#eval swapAt somePattern 1 3

def findSmudge (pattern : List (List Tile)) : Option Nat := do
  let row_num := pattern.length
  let col_num := (←pattern.get? 0).length
  let indices := List.range col_num |> List.map (fun c => (List.range row_num).map (fun r => (c, r))) |> List.join
  let originalNum ← getReflectionNumber pattern

  let stuff := indices.map (fun (c, r) => getReflectionNumber' (swapAt pattern c r) (originalNum))
  match stuff.find? (fun n => n != none) with
  | some (some x) => pure x
  | _ => none

def solvePart1Helper (lines : List String) : Option Nat:= do
  let patternStrings := linesToSegments lines
  let patterns ← patternStrings.mapM parsePattern
  let numbers ← patterns.mapM (fun pattern =>
    getReflectionNumber pattern
  )
  some $ numbers.foldr (Nat.add) 0


def solvePart2Helper (lines : List String) : Option Nat := do
  let patternStrings := linesToSegments lines
  let patterns ← patternStrings.mapM parsePattern
  let numbers ← patterns.mapM findSmudge
  some $ numbers.foldr (Nat.add) 0



def solvePart1 (lines : List String) : Nat :=
  match solvePart1Helper lines with
  | some x => x
  | none => 0


def solvePart2 (lines : List String) : Nat :=
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
      | "part2" =>
        let lines := (←getLines (args.get (Fin.mk 1 inBounds))).reverse
        IO.println (solvePart2 lines)

      | _ => IO.println "Wrong argument, should be 'part1' or 'part2'"
  else
    IO.println ("not enough args")
