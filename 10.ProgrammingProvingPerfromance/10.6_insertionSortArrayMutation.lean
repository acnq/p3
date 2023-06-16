-- Insertion Sort and Array Mutation

#check dbgTraceIfShared 

-- It takes a string and a value as arguments, 
-- and prints a message that uses the string to standard error 
-- if the value has more than one reference, 
-- returning the value. 

-- Inner Loop 
def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α := 
  match i with 
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    have : i' < arr.size := by 
      simp [Nat.lt_of_succ_lt, *]
    match Ord.compare arr[i'] arr[i] with 
    | .lt | .eq => arr 
    | .gt =>
      insertSorted (arr.swap ⟨i', by assumption⟩ i) ⟨i', by simp [*]⟩ 