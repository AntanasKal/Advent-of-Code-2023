import Std.Data.RBMap
import Std.Data.RBMap.Basic
import Std.Data.Nat.Gcd
import Std.Data.Nat.Basic
-- import Std.Data
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

inductive Direction
  | L
  | R

structure LetterTriple where
  first : Char
  second : Char
  third : Char
  deriving Repr, Ord


def parseLR (str : String) : Option (List Direction) :=
  str.toList.mapM (fun x =>
    match x with
    | 'L' => some Direction.L
    | 'R' => some Direction.R
    | _ => none
  )

def parseLetterTriple (line : String) : Option (LetterTriple × LetterTriple × LetterTriple) := do
  let chars := line.toList
  let key := LetterTriple.mk
    (←chars.get? 0)
    (←chars.get? 1)
    (←chars.get? 2)
  let left := LetterTriple.mk
    (←chars.get? 7)
    (←chars.get? 8)
    (←chars.get? 9)
  let right := LetterTriple.mk
    (←chars.get? 12)
    (←chars.get? 13)
    (←chars.get? 14)
  pure (key, left, right)
#eval parseLetterTriple "AAA = (BdB, CCD)"

-- def parseLetterTriples (lines : List String) : Option (List LetterTriples) :=
def LetterTripleMap := Std.RBMap LetterTriple (LetterTriple × LetterTriple) compare

def constructRBMapHelper (triples : List (LetterTriple × LetterTriple × LetterTriple)) (soFar : LetterTripleMap)
  : LetterTripleMap := match triples with
  | [] => soFar
  | (key, left, right)::xs => constructRBMapHelper xs (soFar.insert key (left, right))

def constructRBMap (triples : List (LetterTriple × LetterTriple × LetterTriple))
  : Std.RBMap LetterTriple (LetterTriple × LetterTriple) compare := constructRBMapHelper triples Std.RBMap.empty

def getNextDirection (fullDirections : List Direction) (currentDirections : List Direction) : (Direction × (List Direction)) :=
  match fullDirections, currentDirections with
  | _, (y::ys) => (y, ys)
  | (x::xs), [] => (x, xs)
  | [],[] => (Direction.L, fullDirections) --

def getNextTriple (rbMap : LetterTripleMap) (currentTriple : LetterTriple) (direction : Direction) : LetterTriple :=
  match (rbMap.find? currentTriple), direction with
  | none, _ => currentTriple
  | some (left, _), Direction.L => left
  | some (_, right), Direction.R => right
  -- match maybeTriple
  -- match currentTriple, direction with
  -- | ()
  -- rbMap.find

def countSteps (fullDirections : List Direction) (rbMap : LetterTripleMap) (currentTriple : LetterTriple) (currentDirections : List Direction) (stepsSoFar : Nat) (maxSteps : Nat) : Nat :=
  let (currentDir, newDirs) := getNextDirection fullDirections currentDirections
  let newTriple := getNextTriple rbMap currentTriple currentDir
  match newTriple, stepsSoFar, maxSteps with
  | LetterTriple.mk 'Z' 'Z' 'Z', _, _ => stepsSoFar+1
  | _, _, 0 => 0
  | _, _, k+1 => countSteps fullDirections rbMap newTriple newDirs (stepsSoFar+1) (k)

def countSteps' (fullDirections : List Direction) (rbMap : LetterTripleMap) (currentTriple : LetterTriple) (currentDirections : List Direction) (stepsSoFar : Nat) (maxSteps : Nat) : Nat :=
  let (currentDir, newDirs) := getNextDirection fullDirections currentDirections
  let newTriple := getNextTriple rbMap currentTriple currentDir
  match newTriple.third, stepsSoFar, maxSteps with
  | 'Z', _, _ => stepsSoFar+1
  | _, _, 0 => 0
  | _, _, k+1 => countSteps' fullDirections rbMap newTriple newDirs (stepsSoFar+1) (k)

def countSteps2 (fullDirections : List Direction) (rbMap : LetterTripleMap) (currentTriples : List LetterTriple) (currentDirections : List Direction) (stepsSoFar : Nat) (maxSteps : Nat) : Nat :=
  let (currentDir, newDirs) := getNextDirection fullDirections currentDirections
  let newTriples := currentTriples.map (fun x => getNextTriple rbMap x currentDir)
  match newTriples.all (·.third == 'Z'), stepsSoFar, maxSteps with
  | true, _, _ => stepsSoFar+1
  | _, _, 0 => 0
  | _, _, k+1 => countSteps2 fullDirections rbMap newTriples newDirs (stepsSoFar+1) (k)


def solvePart1Helper (lines : List String) : Option Nat := do
  let lrDirs ← (←lines.get? 0) >>= parseLR
  let triples ← (lines.drop 2).mapM parseLetterTriple
  let rbMap := constructRBMap triples
  let steps := countSteps lrDirs rbMap (LetterTriple.mk 'A' 'A' 'A') lrDirs 0 100000000
  pure steps



def solvePart2Helper (lines : List String) : Option Nat := do
  let lrDirs ← (←lines.get? 0) >>= parseLR
  let triples ← (lines.drop 2).mapM parseLetterTriple
  let endsWithA := triples |> List.map (fun (key, _, _) => key) |> List.filter (·.third == 'A')
  let rbMap := constructRBMap triples
  -- let steps := countSteps2 lrDirs rbMap (endsWithA) lrDirs 0 10000000000
  -- This is a wrong solution, but the inputs are crafted in this way, which is annoying
  let stepList := endsWithA.map (fun x => countSteps' lrDirs rbMap x lrDirs 0 100000000)
  let steps := stepList.foldr Nat.lcm 1
  pure steps


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
