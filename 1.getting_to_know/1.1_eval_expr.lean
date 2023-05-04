
#eval 1 + 2

#eval 1 + 2 * 5

open String
#eval String.append "Hello, " "Lean!"

#eval String.append "great " (String.append "oak " "tree")

#eval String.append "it is " (if 1 > 2 then "yes" else "no")

-- Message
-- #eval String.append "it is "
-- expression
--   String.append "it is "
-- has type
--   String → String
-- but instance
--   Lean.MetaEval (String → String)
-- failed to be synthesized, this instance instructs Lean on how to display the resulting value, recall that any type implementing the `Repr` class also implements the `Lean.MetaEval` class
