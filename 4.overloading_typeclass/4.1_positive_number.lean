
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

-- def seven : Pos := 7
-- failed to synthesize instance
--  OfNat Pos 7

def seven : Pos := 
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))

-- def fourteen : Pos := seven + seven
-- failed to synthesize instance
--   HAdd Pos Pos ?m.235

-- def fortyNine : Pos := seven * seven
-- failed to synthesize instance
--   HMul Pos Pos ?m.291

-- Classes and Instances
class Plus (α : Type) where
  plus : α → α → α  

-- type classes : Plus, overloaded operation : plus
-- (Type class are 1st classes, Plus's type is Type → Type)

instance : Plus Nat where
  plus := Nat.add
-- instantiation of Plus
#eval Plus.plus 5 3

open Plus (plus)
#eval plus 5 3

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k 
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

def fourteen : Pos := plus seven seven 

-- #eval plus 5.2 917.25861
-- failed to synthesize instance
--   Plus Float

-- Overloaded Addition
-- HAdd : heterogenenous addition

instance : Add Pos where
  add := Pos.plus

def fourteen' : Pos := seven + seven

-- conversion to strings

def posToString (atTop : Bool) (p : Pos) : String := 
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match  p with 
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"

instance : ToString Pos where
  toString := posToString true

#eval s!"There are {seven}"

def Pos.toNat : Pos → Nat 
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1

instance : ToString Pos where
  toString x := toString (x.toNat)

#eval s!"There are {seven}" -- most recent take precedence

-- Overloaded Multiplication
-- HMul.hMul 

def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k 
  | Pos.succ n, k => n.mul k + k 

instance : Mul Pos where
  mul := Pos.mul

#eval [ seven * Pos.one, 
        seven * seven,
        Pos.succ Pos.one * seven]

-- Literal Numbers
namespace Hidden
class OfNat (α : Type) (_ : Nat) where
  ofNat : α 
end Hidden

inductive LT4 where
  | zero
  | one
  | two
  | three
deriving Repr 

instance : OfNat LT4 0 where
  ofNat := LT4.zero

instance : OfNat LT4 1 where
  ofNat := LT4.one

instance : OfNat LT4 2 where
  ofNat := LT4.two

instance : OfNat LT4 3 where
  ofNat := LT4.three

#eval (3 : LT4)
-- #eval (4 : LT4)
-- failed to synthesize instance
-- OfNat LT4 4

instance : OfNat Pos (n + 1) where
  ofNat := 
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n 

def eight : Pos := 8
-- def zero : Pos := 0
-- failed to synthesize instance
--   OfNat Pos 0


-- Exercise 
-- 1. Another Representation
structure Pos' where
  succ ::
  pred : Nat
deriving Repr

def one : Pos' := Pos'.succ 0
def two : Pos' := Pos'.succ 1

def Pos'.plus : Pos' → Pos' → Pos'
  | Pos'.succ n, Pos'.succ k => Pos'.succ (1 + n + k)
instance : Add Pos' where
  add := Pos'.plus

def Pos'.mul : Pos' → Pos' → Pos'
  | Pos'.succ 0, k => k
  | Pos'.succ n, Pos'.succ k => Pos'.succ ( n + k + n * k)
instance: Mul Pos' where
  mul := Pos'.mul

#eval one + one 
#eval two * one 


def Pos'.toNat : Pos' → Nat 
  | Pos'.succ n => n + 1

instance : ToString Pos' where
  toString x := toString (x.toNat)

#eval s!"there are {one}"


instance : OfNat Pos' (n + 1) where
  ofNat := 
    let natPlusOne : Nat → Pos'
      | k => Pos'.succ k
    natPlusOne n 
def eight' : Pos' := 8
#eval eight'

-- Even Numbers

structure Even where
  double :: 
  core : Nat 
deriving Repr

def zero2 : Even := Even.double 0
def four : Even := Even.double 2

def Even.plus : Even → Even → Even
  | Even.double n, Even.double k => Even.double (n + k)
instance : Add Even where
  add := Even.plus

def Even.mul : Even → Even → Even
  | Even.double 0, k => Even.double 0
  | Even.double n, Even.double k => Even.double ( 2 * n * k)
instance: Mul Even where
  mul := Even.mul

#eval four + four
#eval four * four


def Even.toNat : Even → Nat 
  | Even.double n => n * 2

instance : ToString Even where
  toString x := toString (x.toNat)

#eval s!"there are {four}"

-- 3. HTTP
-- define inductive type for subset of HTTP method

inductive HTTPMethod
  | GET
  | POST
  | PUT 
  | DELETE

-- define structure of HTTP response
structure HTTPResponse where
  status : Nat
  body : string

def natToString (n : Nat) : String :=
  toString n 
namespace HTTPResponse

-- define  a custom toString funct for HTTP response
def to_string (response : HTTPResponse) : String := 
  "Status : " ++ toString response.status ++ "\nBody: " ++ response.body

instance : ToString HTTPResponse where
  toString x := x.to_string
end HTTPResponse

-- Define  a type class to 
-- associate different IO actions with each HTTP methods
class HTTPHandler (m : Type → Type) :=
  (handle : HTTPMethod → String → m Unit)

instance : HTTPHandler IO := {
  handle := λ method url =>
    match method with
    | .GET     => IO.println $ "Performing GET request to " ++  url
    | .POST    => IO.println $ "Performing POST request to " ++ url
    | .PUT     => IO.println $ "Performing PUT request to " ++ url
    | .DELETE  => IO.println $ "Performing DELETE request to " ++ url
}

def testHarness {m : Type → Type} [Monad m] [HTTPHandler m] : m Unit := do
  HTTPHandler.handle .GET "https://example.com"
  HTTPHandler.handle .POST "https://example.com"
  HTTPHandler.handle .PUT "https://example.com"
  HTTPHandler.handle .DELETE "https://example.com"


-- run the  test harness in the IO monad
def main : IO Unit :=
  testHarness

-- Entry point to execute the IO action
def run : IO Unit := 
  main

