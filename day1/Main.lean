
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

def getFirstDigit (chars : List Char) : Option Nat :=
  match chars with
  | x::xs =>
    if x.isDigit then
      some (x.toNat - 48)
    else
      getFirstDigit xs
  | [] => none

def getLastDigit (chars : List Char) : Option Nat :=
  getFirstDigit (chars.reverse)

def getLineNumber (str : String) : Nat :=
  match getFirstDigit str.toList, getLastDigit str.toList with
  | some first, some last => (first * 10) + last
  | _, _ => 0

def digitsSpelled : List ((List Char) × Nat) :=
  [
      ("zero", 0)
    , ("one", 1)
    , ("two", 2)
    , ("three", 3)
    , ("four", 4)
    , ("five", 5)
    , ("six", 6)
    , ("seven", 7)
    , ("eight", 8)
    , ("nine", 9)
  ].map (fun (x, y) => (x.toList, y))

def startsWithSomeSubstring (str : List Char) (substringMap : List (List Char × Nat)): Option Nat :=
  match substringMap with
  | [] => none
  | x::xs =>
    if str.take x.fst.length == x.fst then
      some x.snd
    else
      startsWithSomeSubstring str xs


def getDigit2 (substringMap : List (List Char × Nat)) (chars : List Char) : Option Nat :=
  match startsWithSomeSubstring chars substringMap with
  | some number => some number
  | none =>
    match chars with
    | x::xs =>
      if x.isDigit then
        some (x.toNat - 48)
      else
        getDigit2 substringMap xs
    | [] => none

def getFirstDigit2 : (chars : List Char) → Option Nat :=
  getDigit2 digitsSpelled

def getLastDigit2 : List Char → Option Nat :=
  getDigit2 (digitsSpelled.map (fun (x, y) => (x.reverse, y)))

def getLineNumber2 (str : String) : Nat :=
  match getFirstDigit2 str.toList, getLastDigit2 str.toList.reverse with
  | some first, some last => (first * 10) + last
  | _, _ => 0


def main (args : List String): IO Unit :=
  if inBounds : 1 < args.length then
    do
      have inBounds0 : 0 < args.length := by
        exact Nat.lt_trans (Nat.zero_lt_one) (inBounds)
      match args.get ⟨0, inBounds0⟩ with
      |"part1" =>
        let lines ← getLines (args.get (Fin.mk 1 inBounds))
        let result1 := List.foldl (Nat.add) (0 : Nat) (List.map getLineNumber lines)
        IO.println result1
      | "part2" =>
        let lines ← getLines (args.get (Fin.mk 1 inBounds))
        let result2 := List.foldl (Nat.add) (0 : Nat) (List.map getLineNumber2 lines)
        IO.println result2
      | _ => IO.println "Wrong argument, should be 'part1' or 'part2'"
  else
    IO.println ("not enough args")
