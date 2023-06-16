-- Indices, Parameters, and Universe Levels

-- an inductive type may have the same universe level as a parameter, 
-- but it must be in a larger universe than its indices. 

-- definition of an inductive type takes its parameters before a colon 
-- and its indices after the colon

inductive Vect (α : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)
--  α is a parameter and the Nat is an index

inductive WithParameter (α : Type u) : Type u where 
  | test : α → WithParameter α  

inductive WithTwoParameters (α : Type u) (β : Type v) : Type (max u v) where
  | test : α → β → WithTwoParameters α β

-- Lean attempts to identify arguments that are described like indices (after the colon), 
--- but used like parameters, and turn them into parameters

inductive WithParameterAfterColon : Type u → Type u where 
  | test : α → WithParameterAfterColon α 

inductive WithParameterAfterColon2 : Type u → Type u where
  | test1 : α → WithParameterAfterColon2 α 
  | test2 : WithParameterAfterColon2 α 

-- differnt names acceptable if not initially declared s
inductive WithParameterAfterColonDifferentNames : Type u → Type u where
  | test1 : α → WithParameterAfterColonDifferentNames α 
  | test2 : β → WithParameterAfterColonDifferentNames β 
-- but not explicitly declared names 
-- inductive WithParameterBeforeColonDifferentNames (α : Type u) : Type u where
--   | test1 : α → WithParameterBeforeColonDifferentNames α
--   | test2 : β → WithParameterBeforeColonDifferentNames β
-- inductive datatype parameter mismatch
--   β
-- expected
--   α
-- no name to index 
-- inductive WithNamedIndex (α : Type u) : Type (u + 1) where
--   | test1 : WithNamedIndex α
--   | test2 : WithNamedIndex α → WithNamedIndex α → WithNamedIndex (α × α)
-- inductive datatype parameter mismatch
--   α × α
-- expected
--   α

inductive WithIndex : Type u → Type (u + 1) where
  | test1 : WithIndex α 
  | test2 : WithIndex α → WithIndex α → WithIndex (α × α)

-- param must come before indices
-- inductive ParamAfterIndex : Nat → Type u → Type u where
--   | test1 : ParamAfterIndex 0 γ
--   | test2 : ParamAfterIndex n γ → ParamAfterIndex k γ → ParamAfterIndex (n + k) γ
-- invalid universe level in constructor 'ParamAfterIndex.test1', parameter 'γ' has type
--   Type u
-- at universe level
--   u+2
-- it must be smaller than or equal to the inductive datatype universe level
--   u+1

-- param can't be types
-- inductive NatParam (n : Nat) : Nat → Type u where
--   | five : NatParam 4 5 
-- inductive datatype parameter mismatch
--   4
-- expected
--   n

inductive NatParam (n : Nat) : Nat → Type u where
  | five : NatParam n 5 

-- rules
-- 1.param identically used in each constructor's type
-- 2. all params before all indices
-- 3. unv level of the datatype defined must be 
-- >= largest param, > largest index
-- 4. named args before colon are param
-- args after colon typically indcs, but lean determine the usage
-- of arg after colon
-- making'em params if
-- they are used consistently in all constructors and don't come after indcs

#print Vect 
-- inductive Vect.{u} : Type u → Nat → Type u
-- number of parameters: 1
-- constructors:
-- Vect.nil : {α : Type u} → Vect α 0
-- Vect.cons : {α : Type u} → {n : Nat} → α → Vect α n → Vect α (n + 1)


