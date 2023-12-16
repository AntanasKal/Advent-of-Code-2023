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


inductive Tile where
  | NS
  | WE
  | NE
  | ES
  | SW
  | WN
  | S
  | Empty
  deriving Ord, BEq

def parseChar : Char → Tile
  | '|' => Tile.NS
  | '-' => Tile.WE
  | 'L' => Tile.NE
  | 'F' => Tile.ES
  | '7' => Tile.SW
  | 'J' => Tile.WN
  | 'S' => Tile.S
  | _ => Tile.Empty

-- def connects ()
-- #eval List.find

-- def findStartingPointInLine (tiles : List Tile) : Option Nat :=

-- def findStartingPoint (tiles : List (List Tile)) : some Nat × Nat :=

def connectsNorth : (Tile) → Bool
  | Tile.NS | Tile.NE | Tile.WN | Tile.S => True
  | _ => False

def connectsEast : (Tile) → Bool
  | Tile.WE | Tile.NE | Tile.ES | Tile.S => True
  | _ => False

def connectsSouth : (Tile) → Bool
  | Tile.NS | Tile.SW | Tile.ES | Tile.S => True
  | _ => False

def connectsWest : (Tile) → Bool
  | Tile.WE | Tile.SW | Tile.WN | Tile.S => True
  | _ => False

def potentiallyConnecting : (Tile × Nat × Nat) → List (Nat × Nat)
  | (tile, x, y) =>
      let toNorth := if connectsNorth tile && y>0 then [(x,y-1)] else []
      let toSouth := if connectsSouth tile
        -- && (map.get? (y+1) != none)
        then [(x,y+1)] else []
      let toEast := if connectsEast tile
        -- && (map.get? y >>= (fun ls => List.get? ls (x+1)) != none)
        then [(x+1,y)] else []
      let toWest := if connectsWest tile && x>0 then [(x-1,y)] else []
      toNorth ++ toSouth ++ toEast ++ toWest

def connects : (Tile × Nat × Nat) → (Tile × Nat × Nat) -> Bool
  | (tile1, x1, y1), (tile2, x2, y2) =>
    (potentiallyConnecting (tile1, x1, y1)).any (·==(x2,y2)) &&
      (potentiallyConnecting (tile2, x2, y2)).any (·==(x1,y1))

def getConnecting (map : List (List (Tile × Nat × Nat))) : (Tile × Nat × Nat) → List (Tile × Nat × Nat)
  | (tile, x, y) =>
    let stuff :=
      potentiallyConnecting (tile, x, y) |> List.map (fun (xCoord, yCoord) => (map.get? yCoord >>= (fun ls => List.get? ls xCoord)))
      |> List.filter (·!=none) |> List.mapA id --|> List. --|> List.filter (connects map (tile, x, y))
    -- let newStuff := stuff.
    match stuff with
    | none => []
    | some list => list.filter (connects (tile, x, y))
    -- []

-- def getNeighbours (map : List (List (Tile × Nat × Nat))) : (Tile × Nat × Nat) → List (Tile × Nat × Nat)
--   | (tile, x, y) =>
--     potentiallyConnecting (tile, x, y) |> List.map (fun (xCoord, yCoord) =>
--     )

partial def countSteps (map : List (List (Tile × Nat × Nat)))  (dir1 prevDir1 dir2 prevDir2 : (Tile × Nat × Nat)) (stepsSoFar : Nat) (maxSteps : Nat) : Nat :=
  if stepsSoFar >= maxSteps
    then 0
  else
    if dir1 == dir2 || dir1 == prevDir2 || prevDir1 == dir2 then stepsSoFar
  else
    let optionNewDir1 := ((getConnecting map dir1).filter (· != prevDir1)).get? 0
    let optionNewDir2 := ((getConnecting map dir2).filter (· != prevDir2)).get? 0
    match optionNewDir1, optionNewDir2 with
    | some newDir1, some newDir2 => countSteps map newDir1 dir1 newDir2 dir2 (stepsSoFar+1) maxSteps
    | _, _ => stepsSoFar

partial def getLoop (map : List (List (Tile × Nat × Nat)))  (dir1 prevDir1 startingDir : (Tile × Nat × Nat)) (loopSoFar : List (Tile × Nat × Nat)) (maxSteps : Nat) : List (Tile × Nat × Nat) :=
  if loopSoFar.length >= maxSteps
    then []
  else
    if dir1 == startingDir then dir1::loopSoFar
  else
    let optionNewDir1 := ((getConnecting map dir1).filter (· != prevDir1)).get? 0
    -- let optionNewDir2 := ((getConnecting map dir2).filter (· != prevDir2)).get? 0
    match optionNewDir1 with
    | some newDir1 => getLoop map newDir1 dir1 startingDir (dir1::loopSoFar) maxSteps
    | _=> [] --loopSoFar
  -- termination_by countSteps map d1 pd1 d2 pd2 stepsSoFar maxSteps => maxSteps - stepsSoFar
def PI := 3.141592
def isInside (x y : Nat) (list : List (Tile × Nat × Nat)) (accumulatedAngle : Float) : Bool  :=
  match list with
  | [] | [tile] => accumulatedAngle.abs > 0.5
  | (tile1::tile2::tiles) =>
    let vec1 := (tile1.snd.fst.toFloat - x.toFloat, tile1.snd.snd.toFloat - y.toFloat)
    let vec2 := (tile2.snd.fst.toFloat - x.toFloat, tile2.snd.snd.toFloat - y.toFloat)
    let currentAngle := Float.acos $ ((vec1.fst * vec2.fst) + (vec1.snd * vec2.snd)) / (Float.sqrt $ (vec1.fst^2 + vec1.snd^2) * (vec2.fst^2 + vec2.snd^2))
    let currentAngle2 := (Float.atan2 vec2.snd vec2.fst) - (Float.atan2 vec1.snd vec1.fst)
    let currentAngle3 := if currentAngle2 > PI then currentAngle2 - (2*PI) else if currentAngle2 < -PI then currentAngle2 + (2*PI) else currentAngle2
    isInside x y (tile2::tiles) (currentAngle3 + accumulatedAngle)

def solvePart1Helper (lines : List String) : Option Nat := do
  let tiles := lines.map (fun line => line.toList.map parseChar)
  let stuff := tiles.zip (List.range tiles.length) |> List.map (fun (line, yCoord) => line.zip (List.range line.length |> List.map (fun (x) => (x, yCoord))))
  let startingTile  ←(←stuff.find? (·.any (fun (t, x, y) => t == Tile.S))).find? (fun (t, x, y) => t == Tile.S)

  let neighbours := getConnecting stuff startingTile
  let dir1Tile ← neighbours.get? 0
  let dir2Tile ← neighbours.get? 1
  -- some 7
  countSteps stuff dir1Tile startingTile dir2Tile startingTile 1 100000




def solvePart2Helper (lines : List String) : Option Nat := do
  let tiles := lines.map (fun line => line.toList.map parseChar)
  let stuff := tiles.zip (List.range tiles.length) |> List.map (fun (line, yCoord) => line.zip (List.range line.length |> List.map (fun (x) => (x, yCoord))))
  let startingTile  ←(←stuff.find? (·.any (fun (t, x, y) => t == Tile.S))).find? (fun (t, x, y) => t == Tile.S)

  let neighbours := getConnecting stuff startingTile
  let dir1Tile ← neighbours.get? 0
  -- some 7
  let loop := getLoop stuff dir1Tile startingTile startingTile [startingTile] 100000
  -- loop.length.toFloat
  let stuff2 :=
    -- stuff.map (fun line => ((line.filter (fun x => !(loop.contains x))).filter (fun (t, x, y) => isInside x y loop 0))
    stuff.map (fun line => ((line.filter (fun x => !(loop.contains x))).filter (fun (t, x, y) => isInside x y loop 0))
    |> List.length)
    |> List.foldr (Nat.add) 0
  stuff2
  -- isInside 5 6 loop 0
  -- countSteps stuff dir1Tile startingTile startingTile [startingTile] 100000


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
        -- IO.println (solvePart1Helper' lines)
      | "part2" =>
        let lines := (←getLines (args.get (Fin.mk 1 inBounds))).reverse
        IO.println (solvePart2 lines)

      | _ => IO.println "Wrong argument, should be 'part1' or 'part2'"
  else
    IO.println ("not enough args")
