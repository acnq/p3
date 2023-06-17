-- Special Types

-- List is de facto a Link List chasing ptrs

-- exception: UInt32, Nat, runtime 
-- and types and proofs are erased from compiled code, take no space

-- Type           | Logical repr                  | runtime repr
-- Nat            | Unary,ptr to Nat.suc          | arbitray-precision int
-- Int            | sum of pos Nat and neg Nat    | Ibid
-- UInt           | Fin with bound                | Fixed-precision machine int
-- Char           | UInt32 paired with prf        | Ordinary char
-- Srring         | struct with .data as List Char| UTF-8 encoded string
-- Array α        | struct with .data as List α   | array of ptr to α values 
-- Sort u         | a type                        | erased completely
-- Prfs of Prop   | prfs                          | erased 