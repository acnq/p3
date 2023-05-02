-- Functions and Definitions

def hello := "Hello"

def lean : String := "Lean"

#eval String.append hello (String.append " " lean)


-- defining functions
def add1 (n : Nat) : Nat := n + 1

#eval add1 7 

def maximum (n : Nat) (k : Nat) : Nat := 
  if n < k then 
    k 
  else n 

#eval maximum (5 + 8) ( 2 * 7)

#check add1

#check (add1)
#check (maximum)

def joinStringWith (a : String) (b : String) (c : String): String := 
  String.append b (String.append a c)
#eval joinStringWith ", " "one" "and another"
#check joinStringWith ": "

def volume (a : Nat) (b : Nat) (c : Nat) := 
  a * b * c 

#eval volume 4 5 6

-- Defining Types
def Str : Type := String

def aStr : Str := "This is a string"

#eval aStr

-- Messages You May Meet 
def NaturalNumber : Type := Nat 

-- def thirtyEigth : NaturalNumber := 38
-- failed to synthesize instance
--   OfNat NaturalNumber 38

def thirtyEigth : NaturalNumber := (38 : Nat)

abbrev N : Type := Nat 
def thirtyNine : N := 39

