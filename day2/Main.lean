
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


def parseSingleColourString (str : String) : Option (Nat × String) :=
  do
    let substrings := (str.dropWhile (· == ' ')).splitOn " "
    let number ← (substrings.get? 0) >>= String.toNat?
    let colour ← (substrings.get? 1)
    pure (number, colour)

def parseSingleDrawString (str : String) : Option (Nat × Nat × Nat) :=
  do
    let singleColourStrings := str.splitOn ","
    let parsedStrings ← List.mapM parseSingleColourString singleColourStrings
    let red := ((parsedStrings.filter (·.snd == "red")).map (·.fst)).foldl (·+·) 0
    let green := ((parsedStrings.filter (·.snd == "green")).map (·.fst)).foldl (·+·) 0
    let blue := ((parsedStrings.filter (·.snd == "blue")).map (·.fst)).foldl (·+·) 0
    pure (red, green, blue)

#eval parseSingleDrawString " 3 red,  5 green,  4 blue "

def parseGame (str : String) : Option (Nat × List (Nat × Nat × Nat)) :=
  let x := str.drop 5 -- Drop "Game " substring
  let y := x.splitOn ":"
  do
    let id ← (y.get? 0) >>= String.toNat?
    let allDrawsString ← y.get? 1
    let singleDrawStrings := allDrawsString.splitOn ";"
    let parsedDraws ← singleDrawStrings.mapM parseSingleDrawString
    pure (id, parsedDraws)

def solvePart1 (lines : List String) : Nat :=
  let optionParsedGames := lines.mapM parseGame
  match optionParsedGames with
  | some parsedGames =>
    let filteredGames := parsedGames.filter (fun game =>
      game.snd.all (fun (r, g, b) => (r <= 12) && (g <= 13) && (b <= 14))
    )
    (filteredGames.map (·.fst)).foldr (·+·) 0
  | none => 0


def getGamePower (game : List (Nat×Nat×Nat)) : Nat :=
  let (max_r, max_g, max_b) :=
    game.foldr (fun (r1, g1, b1) (r2, g2, b2) => (max r1 r2, max g1 g2, max b1 b2)) (0, 0, 0)
  max_r * max_g * max_b

def solvePart2 (lines : List String) : Nat :=
  let optionParsedGames := lines.mapM parseGame
  match optionParsedGames with
  | some parsedGames =>
    (parsedGames.map (getGamePower ·.snd)).foldr (Nat.add) 0
  | none => 0

def main (args : List String): IO Unit :=
  if inBounds : 1 < args.length then
    do
      have inBounds0 : 0 < args.length := by
        exact Nat.lt_trans (Nat.zero_lt_one) (inBounds)
      match args.get ⟨0, inBounds0⟩ with
      |"part1" =>
        let lines ← getLines (args.get (Fin.mk 1 inBounds))
        IO.println (solvePart1 lines)
      | "part2" =>
        let lines ← getLines (args.get (Fin.mk 1 inBounds))
        IO.println (solvePart2 lines)
      | _ => IO.println "Wrong argument, should be 'part1' or 'part2'"
  else
    IO.println ("not enough args")
