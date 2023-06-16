-- Safe Array Indices

namespace Hidden 
structure Fin (n : Nat) where
  val : Nat 
  isLt: LT.lt val n
end Hidden

#eval (5 : Fin 8)
#eval (45: Fin 10) -- modulo is used 

def findHelper (arr : Array α) (p : α → Bool) (i : Nat) : Option (Fin arr.size × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (⟨i, h⟩, x)
    else findHelper arr p (i + 1)
  else none
termination_by findHelper arr p i => arr.size - i

def Array.find (arr : Array α) (p : α → Bool) : Option (Fin arr.size × α) := 
  findHelper arr p 0

  