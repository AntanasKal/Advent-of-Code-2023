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

def List.splitHelper (list : List α) (soFar : List α) (p : α → Bool) : List (List α) :=
  match list, soFar with
  | [], [] => []
  | [], y::ys => [(y::ys).reverse]
  | x::xs, [] => if not (p x) then List.splitHelper xs [x] p else List.splitHelper xs [] p
  | x::xs, y::ys => if not (p x) then List.splitHelper xs (x::y::ys) p else (y::ys).reverse::(List.splitHelper xs [] p)

#eval List.splitHelper [1, 4, 5, 2, 3, 5, 2, 4, 2] [] (·==2)

def List.split (list : List α) (p : α → Bool) : List (List α) := List.splitHelper list [] p

inductive Operation where
  | Dash : Operation
  | Equals : Nat → Operation

structure Step where
  label : String
  op : Operation

def parseStep (str : String) : Option Step := do
  let label := str.takeWhile (Char.isAlpha)
  let opChar ← (str.drop (label.length)).get? 0
  let op ← match opChar with
    | '-' => some Operation.Dash
    | '=' => do
      let num ← (str.drop (label.length +1)).toNat?
      pure (Operation.Equals num)
    | _ => none
  pure ⟨label, op⟩

-- #eval "a.aa.adv".split (·=='.')
def getHash (step : String) : Nat := Id.run
  do
    let mut curr_value := 0
    for c in step.toList do
      curr_value := curr_value + c.toNat
      curr_value := curr_value*17
      curr_value := Nat.mod curr_value 256
    pure curr_value

#eval getHash "pc"

def solvePart1Helper (lines : List String) : Option Nat:= do
  let line ← lines.get? 0
  let stepStrings := line.split (·==',')
  pure $ (stepStrings.map getHash).foldr Nat.add 0

def solvePart2Helper (lines : List String) : Option String := do
  let line ← lines.get? 0
  let stepStrings := line.split (·==',')
  let steps ← stepStrings.mapM parseStep

  let mut boxes : Array (Array (String × Nat)) := Array.mk (List.replicate 256 Array.empty)
  for step in steps do
    let boxNumber := getHash step.label
    if h : boxNumber < boxes.size then
      boxes := boxes.modify boxNumber (fun contents =>
        match step.op with
        | Operation.Dash => contents.filter (·.fst != step.label)
        | Operation.Equals n =>
          match contents.findIdx? (·.fst == step.label) with
          | some i => contents.modify i (fun _ => (step.label, n))
          | none => contents.push (step.label, n)
      )
  let result := boxes.map (fun contents =>
    contents.zip (Array.mk $ (List.range $ contents.size + 1).drop 1)
    |> Array.map (fun triple => (getHash triple.fst.fst +1) * triple.fst.snd * triple.snd
      )
    |> Array.foldr Nat.add 0
  ) |> Array.foldr Nat.add 0
  pure $ toString result

def solvePart1 (lines : List String) : Nat :=
  match solvePart1Helper lines with
  | some x => x
  | none => 0


def solvePart2 (lines : List String) : String :=
  match solvePart2Helper lines with
  | some x => x
  | none => "something bad"

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
