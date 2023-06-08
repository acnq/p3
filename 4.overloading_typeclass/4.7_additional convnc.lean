-- Additional Conveniences

-- construtor syntax for instances
structure Tree : Type where
  latinName : String
  commonName : List String

def oak : Tree := 
  ⟨"Quercus robur", ["common oak", "European oak"]⟩ 

def birch : Tree := 
  {
    latinName := "Betula pendula",
    commonName := ["silver birch", "warty birch"]
  }

def sloe : Tree where 
  latinName := "Prunus spinosa"
  commonName := ["sloe", "blackthorn"]


class Display (α : Type) where
  displayName : α → String

instance : Display Tree := 
  ⟨Tree.latinName⟩

instance : Display Tree := 
  {displayName := Tree.latinName}

instance : Display Tree where 
  displayName t := t.latinName

-- Example
-- definition without a name 

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

example : NonEmptyList String := 
  {
    head := "Sparrow",
    tail := ["Duck", "Swan", "Magpie", "Eurasion coot", "Crow"]
  }

example (n : Nat) (k : Nat) : Bool := 
  n + k == k + n




