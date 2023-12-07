
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

def List.sep' (list : List α) (accum : List α) (p : α → Bool) : List (List α) :=
  match list, accum with
  | nil, nil => []
  | (x::xs), nil => if p x then xs.sep' (accum) p else xs.sep' (x::accum) p
  | nil, _ => [accum]
  | (x::xs), (y::ys) => if p x then (y::ys)::(xs.sep' [] p)  else xs.sep' (x::accum) p

def List.sep (list : List α) (p : α → Bool) : List (List α) :=
  (list.sep' [] p).map .reverse

def parseSeeds (list : List String) : Option (List Nat) := do
  let string ← list.get? 0
  ((string.splitOn " ").drop 1).mapM (String.toNat?)

def getRanges : List Nat → List (Nat × Nat)
  | [] => []
  | x::[] => []
  | x::n::xs => (x,n)::(getRanges xs)

def parseRanges (list : List String) : Option (List (Nat × Nat)) := do
  let string ← list.get? 0
  let nats ← ((string.splitOn " ").drop 1).mapM (String.toNat?)
  pure (getRanges nats)


def parseSingleMapLine (string : String) : Option (Nat × Nat × Nat) := do
  let nums ← (string.splitOn " ").mapM (String.toNat?)
  pure (←nums.get? 0, ←nums.get? 1, ←nums.get? 2)

def parseMap (list : List String) : Option (List (Nat × Nat × Nat)) :=
  (list.drop 1).mapM parseSingleMapLine

def constructMapFunction (mapTriples : List (Nat × Nat × Nat)) : Nat → Nat :=
  fun n =>
    match mapTriples.find? (fun (a, b, c) => b ≤ n && n < b+c) with
    | some (a, b, c) => (n - b) +a
    | none => n

def finalMapFunction (functions : List (Nat → Nat)) (n : Nat) : Nat :=
  match functions with
  | [] => n
  | f::fs => finalMapFunction fs (f n)


def getLocations' (list : List (List String)) : Option (List ( (List (Nat × Nat × Nat))) ):= do
  let list_of_functions := (←(list.drop 1).mapM parseMap)
  list_of_functions


def getMinInRange' (sofar : Nat) (range : Nat × Nat) (function : Nat → Nat) : Nat :=
  match range with
  | (x, 0) => sofar
  | (x, k+1) => getMinInRange' (min (function x) (sofar)) (x+1, k) function
  termination_by getMinInRange' _ range fn => range.snd

def getMinInRange (function : Nat → Nat) (range : Nat × Nat) : Nat :=
  getMinInRange' (function range.fst) (range) function


def mapRange (mapTriple : Nat × Nat × Nat) (range : Nat × Nat) : (List (Nat × Nat)) × (List (Nat × Nat)) :=
  let list := match range, mapTriple with
    | (r, rl), (dst, src, tl) =>
      let a := r
      let b := r+rl-1
      let c := src
      let d:= src+tl-1

      if b < c then
        ([(r, rl)],[])
      else if a ≤ c && b ≤ d then
        ([(a, c-a)],[(dst, b-c+1)])
      else if a ≤ c && d ≤ b then
        ([(a, c-a), (d+1, b-d), (d+1, b-d)],[(dst, d-c+1)])
      else if a ≤ d && b≤ d then
        ([],[(a-c+dst, b-a+1)])
      else if a ≤ d && b≥ d then
        ([(d, b-d)],[(a-c+dst, d-a)])
      else
        ([(r, rl)],[])

  let not_mapped := list.fst.filter (fun (a,b) => b !=0)
  let mapped := list.snd.filter (fun (a,b) => b !=0)
  (not_mapped, mapped)

def List.glue : List (List α) → List α
  | [] => []
  | x::xs => x++(xs.glue)

def applySingleMapping (mapTriples : List (Nat×Nat×Nat)) (ranges : List (Nat × Nat)) : List (Nat × Nat) :=
  match mapTriples with
  | [] => ranges
  | trip::trips =>(ranges.map (fun x=> (mapRange trip x).snd)).glue ++( applySingleMapping trips (ranges.map (fun x=> (mapRange trip x).fst)).glue)

def applyAllMappings (mapTriples : List (List (Nat×Nat×Nat))) (ranges : List (Nat × Nat)) : List (Nat × Nat) :=
  match mapTriples with
  | [] => ranges
  | (x::xs) => applyAllMappings xs (applySingleMapping x ranges)

def getLocations (list : List (List String)) : Option (List Nat) := do
  let seeds ← list.get? 0 >>= parseSeeds
  let ranges := List.map (fun x => (x,1)) seeds
  let mapTriples := (←(list.drop 1).mapM parseMap)
  let finalRanges := applyAllMappings mapTriples ranges
  let locations := finalRanges.map (fun x => x.fst)
  pure locations

def getLocations2 (list : List (List String)) : Option (List Nat) := do
  let ranges ← list.get? 0 >>= parseRanges
  let mapTriples := (←(list.drop 1).mapM parseMap)
  let finalRanges := applyAllMappings mapTriples ranges
  let locations := finalRanges.map (fun x => x.fst)
  pure locations

def solvePart1 (lines : List String) : Nat :=
  let map_string := (lines.sep (String.isEmpty))
  match (getLocations (map_string)) >>= List.minimum? with
  | none => 0
  | some stuff => stuff

def solvePart2 (lines : List String) : Nat :=
  let map_string := (lines.sep (String.isEmpty))
  match (getLocations2 (map_string)) >>= List.minimum? with
  | none => 0
  | some stuff => stuff

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
