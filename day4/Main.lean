
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

-- #eval "asdfads || asdfadsf".isE //.splitOn "|"

def getNumbersList (str : String) : Option (List Nat) := do
  let num_strings := List.filter (fun x => not x.isEmpty) (str.split Char.isWhitespace)
  let nums ← List.mapM String.toNat? num_strings
  pure nums

def parseCards (line : String) : Option (List Nat × List Nat) :=
  do
    let lottery_string ← (line.splitOn ":").get? 1
    let winning_number_string ← (lottery_string.splitOn "|").get? 0
    let ticket_number_string ← (lottery_string.splitOn "|").get? 1
    let winning_numbers ← getNumbersList winning_number_string
    let ticket_numbers ← getNumbersList ticket_number_string
    pure (winning_numbers, ticket_numbers)

def some_line := "Card 1: 41 48 83 86 17 | 83 86  6 31 17  9 48 53"
#eval parseCards some_line
#eval ((some_line.splitOn ":").get? 1)


def getCardScore : (List Nat × List Nat) → Nat
  | (winning_numbers, ticket_numbers) =>
    match ((ticket_numbers.filter winning_numbers.contains).length) with
    | 0 => 0
    | k+1 => 2^k

def getMatchingNumbers : (List Nat × List Nat) → Nat
  | (winning_numbers, ticket_numbers) =>
    ((ticket_numbers.filter winning_numbers.contains).length)


def solvePart1 (lines : List String) : Nat :=
  match lines.mapM parseCards with
  | none => 0
  | some list => (getCardScore <$> list).foldr (Nat.add) 0

def addSolving (list : List (Nat × Nat)) (ticket_amount : Nat) (subsequence_length : Nat) : List (Nat × Nat) :=
  match list, subsequence_length with
  | [], _ => []
  | _, 0 => list
  | (tickets, matching_numbs)::xs, k+1 => (tickets+ticket_amount, matching_numbs)::(addSolving xs ticket_amount k)

theorem add_solving_length : ∀ (list : List (Nat × Nat)) (x : Nat) (y : Nat) , (addSolving list x y).length = list.length := by
  intro list
  induction list with
  | nil => intro x y; simp[addSolving]
  | cons head tail tail_ih =>
    intro x y;
    match y with
    | 0 => rfl
    | k+1 =>
      simp [addSolving, tail_ih]




def playGame : (List (Nat × Nat)) → List (Nat × Nat)
  | [] => []
  | (tickets, matching_numbers)::xs =>
    have helper : (addSolving xs (tickets) matching_numbers).length = xs.length := by rw[add_solving_length]
    have thm : List.length (addSolving xs (tickets) matching_numbers) < Nat.succ (List.length xs) :=
      by rw[helper]; exact (Nat.lt_succ_self (List.length xs))
    (tickets,matching_numbers)::(playGame (addSolving xs (tickets) matching_numbers))
  termination_by playGame ls => ls.length

def solvePart2 (lines : List String) : Nat :=
  match lines.mapM parseCards with
  | none => 0
  | some list =>
    let initial_list := (getMatchingNumbers <$> list).map (fun x => (1,x))
    let end_game := playGame initial_list
    (end_game.map (·.fst)).foldr (Nat.add) 0

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
        -- IO.println "not implemented!"
        let lines ← getLines (args.get (Fin.mk 1 inBounds))
        IO.println (solvePart2 lines.reverse)
      | _ => IO.println "Wrong argument, should be 'part1' or 'part2'"
  else
    IO.println ("not enough args")
