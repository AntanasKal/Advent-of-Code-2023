
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


def getNumbers (line : String) : Option (List Nat) :=
  line.split (Char.isWhitespace) |> List.drop 1 |> List.filter (not $ String.isEmpty ·) |> List.mapM (String.toNat?)

def getNumber (line : String) : Option Nat :=
  line.split (Char.isWhitespace) |> List.drop 1 |> List.filter (not $ String.isEmpty ·) |> String.join |> (String.toNat?)

def getNumberOfWaysToBeatTheRecord (race : Nat × Nat) : Nat :=
  match race with
  | (t, d) => (List.range t).filter (fun x => x*(t-x) > d) |> List.length

def solvePart1Helper (lines : List String) : Option Nat := do
  let times      ← (lines.get? 0) >>= getNumbers
  let distances  ← (lines.get? 1) >>= getNumbers
  let races := List.zip times distances
  pure $ (races.map getNumberOfWaysToBeatTheRecord).foldr (Nat.mul) 1

def solvePart2Helper (lines : List String) : Option Nat := do
  let time      ← (lines.get? 0) >>= getNumber
  let distance  ← (lines.get? 1) >>= getNumber
  pure $ (getNumberOfWaysToBeatTheRecord (time, distance))

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
