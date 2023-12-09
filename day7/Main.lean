
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

-- inductive HandType2
--   | High : Nat → Nat →  Nat → Nat → Nat → HandType2
--   | OnePair : Nat →  Nat → Nat → Nat → HandType2
--   | TwoPair : Nat → Nat → Nat → HandType2
--   | Three : Nat → Nat → Nat → HandType2
--   | FullHouse : Nat → Nat → HandType2
--   | Four : Nat → Nat → HandType2
--   | Five : Nat → HandType2
--   deriving Repr, Ord

-- #eval (compare (HandType2.High 5 4 3 2 1) (HandType2.High 5 5 2 2 2)).toCtorIdx

-- def getHandType2 (list : List Nat) : Option HandType2 := do
--   let frequencies := possibleNats.map (fun x => (list.filter (x==·)).length)
--   let frequenciesZipped := frequencies.zip possibleNats
--   match frequencies.toArray.insertionSort (·>·) |> Array.toList with
--   | 5::_ => HandType2.Five (← frequenciesZipped.find? (·.fst == 5)).snd
--   | 4::_ => HandType2.Four (← frequenciesZipped.find? (·.fst == 4)).snd (← frequenciesZipped.find? (·.fst == 1)).snd
--   | 3::2::_ => HandType2.FullHouse (← frequenciesZipped.find? (·.fst == 3)).snd (← frequenciesZipped.find? (·.fst == 2)).snd
--   | 3::_::_ => HandType2.Three (← frequenciesZipped.find? (·.fst == 3)).snd (← frequenciesZipped.reverse.find? (·.fst == 1)).snd (← frequenciesZipped.find? (·.fst == 1)).snd
--   | 2::2::_ => HandType2.TwoPair (← frequenciesZipped.reverse.find? (·.fst == 2)).snd (← frequenciesZipped.find? (·.fst == 2)).snd (← frequenciesZipped.find? (·.fst == 1)).snd
--   | 2::_ =>
--     let filtered_ones := (frequenciesZipped.filter (·.fst == 1)).toArray.insertionSort (fun x y => x.snd > y.snd)
--     HandType2.OnePair (← frequenciesZipped.find? (·.fst == 2)).snd (← filtered_ones.get? 0).snd (←filtered_ones.get? 1).snd (←filtered_ones.get? 2).snd
--   | _ =>
--     let filtered_ones := (frequenciesZipped.filter (·.fst == 1)).toArray.insertionSort (fun x y => x.snd > y.snd)
--     HandType2.High (←filtered_ones.get? 0).snd (←filtered_ones.get? 1).snd (←filtered_ones.get? 2).snd (←filtered_ones.get? 3).snd (←filtered_ones.get? 4).snd

-- #eval getHandType2 [2, 3, 3, 1, 3]

-- def solvePart1Helper2 (lines : List String) : Option Nat := do
--   let parsedHands ← lines.mapM parseCard2
--   let sortedHands := parsedHands.toArray.insertionSort (fun (x1,y1) (x2, y2) => (compare y1 y2) == Ordering.lt) |> Array.toList
--   let sortedHandsWithPosition := sortedHands.zip ((List.range (sortedHands.length+1)).drop 1)
--   pure $ sortedHandsWithPosition.foldl (fun y ((bid, _), position) => y+bid*position) 0

-- #eval parseCard "55212 28"

-- #eval parseCard "KTJJT 220"

-- #eval (compare HandType.Three HandType.Three).toCtorIdx

def possibleNats : List Nat :=
  (List.range 15).drop 1

inductive HandType where
  | HighCard
  | OnePair
  | TwoPair
  | Three
  | FullHouse
  | Four
  | Five
  deriving Ord, Repr

structure Hand where
  first : Nat
  second : Nat
  third : Nat
  fourth : Nat
  fifth : Nat
  deriving Ord, Repr

structure HandOrdering where
  handType : HandType
  hand : Hand
  deriving Repr, Ord

#eval (compare (Hand.mk 1 3 3 4 5) (Hand.mk 1 2 3 8 5)).toCtorIdx

#eval (compare HandType.Five HandType.TwoPair).toCtorIdx

def isLT : (HandType × Hand) → (HandType × Hand) → Bool
  | (ht1, h1), (ht2,h2) =>
    match (compare ht1 ht2), (compare h1 h2) with
    | Ordering.lt, _ => true
    | Ordering.eq, Ordering.lt => true
    | _, _ => false

def CharToNat : Char → Nat
  | 'A' => 14
  | 'K' => 13
  | 'Q' => 12
  | 'J' => 11
  | 'T' => 10
  | x => if x.isDigit then (x.toNat-48) else 0

def CharToNat2 : Char → Nat
  | 'A' => 14
  | 'K' => 13
  | 'Q' => 12
  | 'J' => 0
  | 'T' => 10
  | x => if x.isDigit then (x.toNat-48) else 0


def getHandType (arr : List Nat) : HandType :=
  let frequencies := possibleNats.map (fun x => (arr.filter (x==·)).length)
  match frequencies.toArray.insertionSort (·>·) |> Array.toList with
  | 5::_ => HandType.Five
  | 4::_ => HandType.Four
  | 3::2::_ => HandType.FullHouse
  | 3::_::_ => HandType.Three
  | 2::2::_ => HandType.TwoPair
  | 2::_ => HandType.OnePair
  | _ => HandType.HighCard

def getCardTuple (list : List Nat) : Option (HandType × Hand) := do
  let handType := getHandType list
  let hand := Hand.mk
    (← list.get? 0)
    (← list.get? 1)
    (← list.get? 2)
    (← list.get? 3)
    (← list.get? 4)
  pure (handType, hand)

def parseCard (line : String) : Option (Nat × HandType × Hand) := do
  let bid ← (line.splitOn " ").get? 1 >>= String.toNat?
  let handInfo ← (← ((line.splitOn " ").get? 0)).toList.map (CharToNat) >>= getCardTuple
  pure (bid, handInfo)



def possibleNats2 : (List Nat) :=
  [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14]

def getStrongestVariant (list : List Nat) : Option HandType := do
  let potentialHandLists := possibleNats2.map (fun x => (list.map fun y => if y == 0 then x else y))
  let potentialHandTypes := List.map getHandType potentialHandLists
  (potentialHandTypes.toArray.insertionSort (fun x y => (compare y x) == Ordering.lt)).get? 0
  -- none

#eval getStrongestVariant [3, 0, 10, 3, 13]

def getCardTuple2 (list : List Nat) : Option (HandType × Hand) := do
  let handType ← getStrongestVariant list
  let hand := Hand.mk
    (← list.get? 0)
    (← list.get? 1)
    (← list.get? 2)
    (← list.get? 3)
    (← list.get? 4)
  pure (handType, hand)

def parseCard2  (line : String) : Option (Nat × HandType × Hand) := do
  let bid ← (line.splitOn " ").get? 1 >>= String.toNat?
  let handInfo ← (← ((line.splitOn " ").get? 0)).toList.map (CharToNat2) >>= getCardTuple2
  pure (bid, handInfo)

def solvePart1Helper (lines : List String) : Option Nat := do
  let parsedHands ← lines.mapM parseCard
  let sortedHands := parsedHands.toArray.insertionSort (fun (x1,y1) (x2, y2) => isLT y1 y2) |> Array.toList
  let sortedHandsWithPosition := sortedHands.zip ((List.range (sortedHands.length+1)).drop 1)
  pure $ sortedHandsWithPosition.foldl (fun y ((bid, _, _), position) => y+bid*position) 0

-- -- deriving instance Repr for :(Nat × HandType × Hand)

def solvePart1Helper' (lines : List String) : Option String := do
  let parsedHands ← lines.mapM parseCard
  -- pure $ toString $ parsedHands.map (fun (a,b,c) => c)
  let sortedHands := parsedHands.toArray.insertionSort (fun (x1,y1) (x2, y2) => isLT y1 y2) |> Array.toList
  let sortedHandsWithPosition := sortedHands.zip ((List.range (sortedHands.length+1)).drop 1)
  pure $ toString $ sortedHands.map (fun x => x.fst)

def solvePart1 (lines : List String) : Nat :=
  match solvePart1Helper lines with
  | some x => x
  | none => 0

def solvePart2Helper (lines : List String) : Option Nat := do
  let parsedHands ← lines.mapM parseCard2
  let sortedHands := parsedHands.toArray.insertionSort (fun (x1,y1) (x2, y2) => isLT y1 y2) |> Array.toList
  let sortedHandsWithPosition := sortedHands.zip ((List.range (sortedHands.length+1)).drop 1)
  pure $ sortedHandsWithPosition.foldl (fun y ((bid, _, _), position) => y+bid*position) 0


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
