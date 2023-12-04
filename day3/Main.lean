
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


def indexList' (accum : Nat) (list : List α) : List (α × Nat) :=
  match list with
  | [] => []
  | x::xs => (x, accum)::(indexList' (accum+1) xs)

def indexList : (List α) → List (α × Nat) := indexList' 0

inductive NonEmptyList (α : Type) where
  | cons : α → List α → NonEmptyList α
deriving Repr

def NonEmptyList.toList : NonEmptyList α → List α
  | cons x xs => x::xs

def NonEmptyList.first : NonEmptyList α → α
  | cons x xs => x

def NonEmptyList.last : NonEmptyList α → α
  | cons x [] => x
  | cons x (y :: ys) => (NonEmptyList.cons y ys).last


def splitToSublists' (accum : List α) (list : List α) (p : α → Bool) : List (NonEmptyList α) :=
  match list, accum with
  | [], [] => []
  | x::xs, [] => if p x then splitToSublists' [x] xs p else splitToSublists' [] xs p
  | [], (y::ys) => [NonEmptyList.cons y ys]
  | x::xs, (y::ys) =>
    if p x then
      splitToSublists' (x::y::ys) xs p
    else
      (NonEmptyList.cons y ys)::(splitToSublists' [] xs p)

#eval splitToSublists' [] [1, 1, 2, 2, 2, 1, 3, 2, 4, 4,2, 89, 55] (fun x => x != 2)

def splitToSublists (list : List α) (p : α → Bool) : List (NonEmptyList α) :=
  splitToSublists' [] list p


def numberFromReversedCharList' (accum : Nat) (power : Nat) (list : List Char) :=
  match list with
  | [] => accum
  | x::xs => numberFromReversedCharList' (accum + (x.toNat - 48)*10^power) (power+1) xs

def numberFromReversedCharList (list : List Char) : Nat :=
  numberFromReversedCharList' 0 0 list

def NonEmptyList.toNumber (list : NonEmptyList (Char × Nat)) : (Nat × Nat × Nat) :=
  let end_x := list.first.snd
  let start_x := list.last.snd
  let number := numberFromReversedCharList (list.toList.map (·.fst))
  (number, start_x, end_x)


#eval splitToSublists (indexList "467..114..".toList) (fun (x, y) => Char.isDigit x)


#eval (splitToSublists (indexList "467..114..".toList) (fun (x, y) => Char.isDigit x)).map (NonEmptyList.toNumber)


def getNumbersInLineList (line : String) : List (Nat × Nat × Nat) :=
  let indexed_list := indexList line.toList
  let sublists := splitToSublists indexed_list (fun (x, y) => Char.isDigit x)
  sublists.map (NonEmptyList.toNumber)

def getAllNumbers' (accum : Nat) (lines : List String) : List (Nat × Nat × Nat × Nat) :=
  match lines with
  | [] => []
  | x::xs => ((getNumbersInLineList x).map (fun (n, s_x, e_x) => (n, s_x, e_x, accum)))++(getAllNumbers' (accum+1) xs)

def getAllNumbers : List String → List (Nat × Nat × Nat × Nat) := getAllNumbers' 0
-- def getAllNumbers (lines : List String) : List (Nat × Nat × Nat × Nat) :=

def getCharsInList (list : List Char) : List (Char×Nat) :=
  (indexList list).filter (fun (x, y) => !x.isDigit && x != '.')


def getAllChars' (accum : Nat) (lines : List String) : List (Nat × Nat) :=
  match lines with
  | [] => []
  | x::xs => (((getCharsInList x.toList).map (·.snd)).map (fun x => (x, accum)))++(getAllChars' (accum+1) xs)

def getAllChars : List String → List (Nat × Nat) := getAllChars' 0


def isAdjacent (number_data : Nat × Nat × Nat × Nat) (char_data : Nat × Nat) : Bool :=
  match number_data, char_data with
  | (_, s_x, e_x, y), (c_x, c_y) =>
    c_x<=e_x+1 && c_x+1>=s_x && c_y <= y+1 && c_y+1 >= y


def solvePart1 (lines : List String) : Nat :=
  let all_number_data := getAllNumbers lines
  let all_char_data := getAllChars lines
  let filtered_numbers := all_number_data.filter
    (fun number_data => (all_char_data.any (isAdjacent number_data)))
  filtered_numbers.foldr (fun (x, y) accum => x+accum) 0


def getGearNumber (all_number_data : List (Nat × Nat × Nat × Nat)) (char_data : Nat × Nat) : Nat :=
  let list_of_neighbours := all_number_data.filter (fun x => isAdjacent x char_data)
  match list_of_neighbours with
  | x::y::[] => x.fst * y.fst
  | _ => 0

def solvePart2 (lines : List String) : Nat :=
  let all_number_data := getAllNumbers lines
  let all_char_data := getAllChars lines
  (all_char_data.map (getGearNumber all_number_data)).foldr (Nat.add) 0

def main (args : List String) : IO Unit :=
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
