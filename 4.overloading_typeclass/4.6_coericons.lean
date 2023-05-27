import Lean
-- Coericions //强转

-- Postive Numbers

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
def Pos.toNat : Pos → Nat 
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1
instance : ToString Pos where
  toString x := toString (x.toNat)
instance : OfNat Pos (n + 1) where
  ofNat := 
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n 
#eval (3 : Pos)
-- #eval [1, 2, 3, 4].drop (2 : Pos)
-- application type mismatch
--   List.drop 2
-- argument
--   2
-- has type
--   Pos : Type
-- but is expected to have type
--   Nat : Type

namespace Hidden
class Coe (α : Type) (β : Type) where 
  coe : α → β  
end Hidden

instance : Coe Pos Nat where
  coe x := x.toNat

#eval [1, 2, 3, 4].drop (2 : Pos)

-- Chaining Coericons
def oneInt : Int := Pos.one

inductive A where
  | a 

inductive B where
  | b 
deriving Repr

instance : Coe A B where
  coe _ := B.b

instance : Coe B A where
  coe _ := A.a

instance : Coe Unit A where
  coe _ := A.a

def coercedToB : B := () -- () used for Unit.unit 
#eval coercedToB

def List.last? : List α → Option α 
  | [] => none
  | [x] => x
  | _ :: x :: xs => last? (x :: xs)

def perhapsPerhapsPerhaps : Option (Option (Option String)) := 
  "Please don't tell me"

-- def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) := 
--   392
-- -- failed to synthesize instance
--   OfNat (Option (Option (Option Nat))) 392
-- since it is a instance missing, not a type mismatch, the coericon is not of help

def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) := 
  (392 : Nat)

def perhapsPerhapsPerhapsNat' : Option (Option (Option Nat)) := 
  ↑(392 : Nat)
-- ↑ as coericon 

-- Non-Empty Lists and Dependent Coericons
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

instance : Coe (NonEmptyList α) (List α) where
  coe
    | {head := x, tail := xs} => x :: xs

namespace Hidden
class CoeDep (α : Type) (x : α) (β : Type) where
  coe : β 
end Hidden

instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := { head := x, tail := xs}

-- Coercing to Types
structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid := 
  { Carrier := Nat, neutral := 1, op := (· * ·)}

def natAddMonoid : Monoid :=
  { Carrier := Nat, neutral := 0, op := (· + ·)}

def stringMonoid : Monoid := 
  { Carrier := String, neutral := "", op := String.append }

def listMonoid (α : Type) : Monoid := 
  { Carrier := List α, neutral := [], op := List.append}

def foldMap (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier := 
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

instance : CoeSort Monoid Type where
  coe m := m.Carrier

def foldMap' (M : Monoid) (f : α → M) (xs : List α) : M := 
  let rec go (soFar : M) : List α → M 
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

instance : CoeSort Bool Prop where
  coe b := b = true

-- Coercing to Functions
namespace Hidden
class CoeFun (α : Type) (makeFunctionType : outParam (α → Type)) where
  coe : (x : α) → makeFunctionType x 
end Hidden

structure Adder where
  howMuch : Nat

def add5 : Adder := ⟨5⟩

-- it is not a function
-- #eval add5 3 
-- function expected at
--   add5
-- term has type
--   Adder
-- we need CoeFun

instance : CoeFun Adder (fun _ => Nat → Nat) where
  coe a := (· + a.howMuch)

#eval add5 3 

inductive JSON where
  | true : JSON
  | false : JSON
  | null : JSON
  | string : String → JSON
  | number : Float → JSON
  | object : List (String × JSON) → JSON
  | array : List JSON → JSON
deriving Repr

structure Serializer where
  Contents : Type 
  serialize : Contents →  JSON

def Str : Serializer := 
  {Contents := String,
    serialize := JSON.string
  }

instance : CoeFun Serializer (fun s => s.Contents → JSON) where
  coe s := s.serialize

def buildResponse (title : String) (R : Serializer) (record : R.Contents) : JSON :=
  JSON.object [
    ("title", JSON.string title),
    ("status", JSON.number 200),
    ("record", R record)
  ]

#eval buildResponse "Functional Programming in Lean" Str "Programming is fun!"

-- Aside : JSON as a String
#eval (5 : Float).toString

def dropDecimals (numString : String) : String := 
  if numString.contains '.' then
    let noTrailingZeros := numString.dropRightWhile (· == '0')
    noTrailingZeros.dropRightWhile (· == '.')
  else numString
#eval dropDecimals (5 : Float).toString
#eval dropDecimals (5.2 : Float).toString

def String.separate (sep : String) (strings : List String) : String :=
  match strings with
    | [] => ""
    | x :: xs => String.join (x :: xs.map (sep ++ ·))

#eval ", ".separate ["1", "2"]
#eval ", ".separate ["1"]
#eval ", ".separate []

partial def JSON.asString (val : JSON) : String := 
  match val with 
    | true => "true"
    | false => "false"
    | null => "null"
    | string s => "\"" ++ Lean.Json.escape s ++ "\""
    | number n => dropDecimals n.toString
    | object members => 
      let memberToString mem := 
        "\"" ++ Lean.Json.escape mem.fst ++ "\": " ++ asString mem.snd  
      "{" ++ ", ".separate (members.map memberToString) ++ "}"
    | array elements =>
      "[" ++  ",".separate (elements.map asString) ++ "]"

#check Lean.Json.escape
#eval (buildResponse "Functional Programming in Lean" Str "Programming is fun!").asString

-- Design Considerations
def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced 蜘蛛"
  ]
}  

def lastSpider : Option String :=
  List.getLast? idahoSpiders

-- However, if type annotation is omitted, 
-- the result type is unkown, so Lean is unable to find the coericons
-- def lastSpider' :=
--   List.getLast? idahoSpiders

-- application type mismatch
--   List.getLast? idahoSpiders
-- argument
--   idahoSpiders
-- has type
--   NonEmptyList String : Type
-- but is expected to have type
--   List ?m.16727 : Type