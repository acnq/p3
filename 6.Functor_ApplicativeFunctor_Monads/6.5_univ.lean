-- Universe
-- A universe is a type that classifies other types

#check Prop
#check Type 

-- User Defined Types

--  in a universe that's large enough 
-- to prevent it from containing its own type
inductive MyList_ (α : Type) : Type where
  | nil : MyList_ α
  | cons : α → MyList_ α → MyList_ α 

-- MyList itself is a Type → Type
-- This means that it cannot be used to contain actual types, 
-- because then its argument would be Type
-- which is a Type 1

-- def myListOfNat : MyList Type :=
--   .cons Nat .nil 

-- application type mismatch
--   MyList Type
-- argument
--   Type
-- has type
--   Type 1 : Type 2
-- but is expected to have type
--   Type : Type 1

-- arg updated to Type 1 is a rejected definition

-- inductive MyList' (α : Type 1) : Type where
--   | nil : MyList' α 
--   | cons : α → MyList' α → MyList' α  

-- invalid universe level in constructor 'MyList.cons', parameter has type
--   α
-- at universe level
--   2
-- it must be smaller than or equal to the inductive datatype universe level
--   1

-- Universe Polymorphism

-- variable represent universe 
-- conventionally u, v, w
inductive MyList (α : Type u) : Type u where
  | nil : MyList α 
  | cons : α → MyList α → MyList α 

def myListOfNumbers : MyList Nat := 
  .cons 0 (.cons 1 .nil)

def myListOfNat : MyList Type := 
  .cons Nat .nil

def myListOfList : MyList (Type → Type) := 
  .cons MyList .nil

-- behind the scene it used copied datatype at each level
-- and choosing which copy to be used to solve the paradox problem
-- the above code can be explicit write as 


def myListOfNumbers_ : MyList.{0} Nat := 
  .cons 0 (.cons 1 .nil)

def myListOfNat_ : MyList.{1} Type := 
  .cons Nat .nil

def myListOfList_ : MyList.{1} (Type → Type) := 
  .cons MyList.{0} .nil

-- each type arg with own level var to reach max flexibility
namespace Hidden
inductive Sum (α : Type u) (β : Type u) : Type u where
  | inl : α → Sum α β 
  | inr : β → Sum α β  


def stringOrNat : Sum String Nat := .inl "hello"
def typeOrType : Sum Type Type := .inr Nat

-- require same universe level 
-- def stringOrType : Sum String Type := .inr Nat 
-- application type mismatch
--   Sum String Type
-- argument
--   Type
-- has type
--   Type 1 : Type 2
-- but is expected to have type
--   Type : Type 1

inductive Sum2 (α : Type u) (β : Type v) : Type (max  u v) where
  | inl : α → Sum2 α β 
  | inr : β → Sum2 α β 

def stringOrType : Sum2 String Type := .inr Nat
end Hidden 

-- Writing Universe-Polymorphic Definitions
-- guidelines:
-- 1. independent type arguments 
-- should have different universe variable
-- 2. he whole type is itself typically 
-- either in the maximum of all the universe variables, 
-- or one greater than this maximum.
-- 3. it's a good idea to put the new type 
-- in as small of a universe as possible

-- Prop and Polymorphism
-- prop is at the bottom of univ hierarchy
def someTruePropositions : List Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]

def someTruePropositions_ : List.{0} Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]

-- Polymorphism in Practice
-- complete def of Functor Applicative Monad