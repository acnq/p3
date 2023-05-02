-- Types

#eval (1 + 2 : Nat) -- Natural Number

#eval 1 - 2 -- protect Natural Number type: 1 - 2 = 0

#eval (1 - 2 : Int) -- integer

-- type mismatch error
-- #check String.append "hello" [" ", "world"]

-- application type mismatch
--   String.append "hello" [" ", "world"]
-- argument
--   [" ", "world"]
-- has type
--   List String : Type
-- but is expected to have type
--   String : Type
