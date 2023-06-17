def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    have : i' < arr.size := by
      simp [Nat.lt_of_succ_lt, *]
    match Ord.compare arr[i'] arr[i] with
    | .lt | .eq => arr
    | .gt =>
      insertSorted
        ((dbgTraceIfShared "array to swap" arr).swap ⟨i', by assumption⟩ i)
        ⟨i', by simp [dbgTraceIfShared, *]⟩

theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → (arr.size = len) →
    (insertSorted arr ⟨i, isLt⟩).size = len := by
  induction i with
  | zero =>
    intro arr isLt hLen
    simp [insertSorted, *]
  | succ i' ih =>
    intro arr isLt hLen
    simp [insertSorted, dbgTraceIfShared]
    split <;> simp [*]

def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
      rw [insert_sorted_size_eq arr.size i arr h rfl]
      simp [Nat.sub_succ_lt_self, *]
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by insertionSortLoop arr i => arr.size - i

def insertionSort [Ord α] (arr : Array α) : Array α :=
  insertionSortLoop arr 0

def getLines : IO (Array String) := do 
  let stdin ← IO.getStdin
  let mut lines : Array String := #[]
  let mut currLine ← stdin.getLine
  while !currLine.isEmpty do 
    -- Drop trailing newline:
    lines := lines.push (currLine.dropRight 1) 
    currLine ← stdin.getLine
  pure lines 

def mainUnique : IO Unit := do 
  let lines ← getLines 
  for line in insertionSort lines do 
    IO.println line 

def mainShared : IO Unit := do 
  let lines ← getLines
  IO.println "--- Sorted lines: ---"
  for line in insertionSort lines do 
    IO.println line 

  IO.println ""
  IO.println "--- Original data: ---"
  for line in lines do 
    IO.println line 

def main (args : List String) : IO UInt32 := do 
  match args with 
  | ["--shared"] => mainShared; pure 0
  | ["--unique"] => mainUnique; pure 0 
  | _ =>
    IO.println "Expected single argument, either \"--shared\" or \"--unique\""
    pure 1 

-- lean -c sort.c sort.lean
-- leanc sort.c -o sort 
-- I test it failed in this terminal, but after paste the source file
-- to desktop it works, don't know the reason
-- refering https://leanprover-community.github.io/archive/stream/270676-lean4/topic/ld64.2Elld.20dynamic.20link.20errors.20on.20MacOS.html
-- it seems an Apple MacOS version problem 
-- "--shared" only work in sort.exe windows platform

-- Other Opportunities for Mutations