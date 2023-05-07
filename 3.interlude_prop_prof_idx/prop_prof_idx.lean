-- interlude: "Hello, ".append "world" = "Hello, world" := by simp
def woodlandCritters : List String := 
  ["hedgehod", "deer", "snail"]

def hedgehod := woodlandCritters[0]
def deer := woodlandCritters[1]
def snail := woodlandCritters[2]

-- def oops := woodlandCritters[3]
-- failed to prove index is valid, possible solutions:
--   - Use `have`-expressions to prove the index is valid
--   - Use `a[i]!` notation instead, runtime check is perfomed, and 'Panic' error message is produced if index is not valid
--   - Use `a[i]?` notation instead, result is an `Option` type
--   - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
-- ⊢ 3 < List.length woodlandCritters

-- Propositions and Proofs
-- propositions are types, 
-- They specify what counts as evidence that the statement is true.
-- `命题是类型`

def onePlusOneIsTwo : 1 + 1 = 2 := rfl

-- def onePlusOneIsFifteen : 1 + 1 = 15 := rfl
-- type mismatch
--   rfl
-- has type
--   1 + 1 = 1 + 1 : Prop
-- but is expected to have type
--   1 + 1 = 15 : Prop

def OnePlusOneIsTwo : Prop := 1 + 1 = 2
theorem onePlusOneIsTwo': OnePlusOneIsTwo := rfl

-- Tactics
-- small programs construct evidence for a proposition
-- proof state, run in a proof state, 
-- proof state tracks statement that is to be proved, i.e. goal
-- along with assumptions that are available to prove it.
-- use `by` puts lean into tactic mode, 
-- until the end of the next indented block
-- In tactic mode, lean provide current proof state.

theorem onePlusOneIsTwo1 : 1 + 1 = 2 := by  
  simp  

theorem oneIsLessThan2 : 1 < 2 := by
  simp

-- Connectives:
-- logical connectives : and or true false, not
theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by simp 

-- Implication (if A then B) is represented using functions.
-- In particular, a function that transforms evidence for A 
-- into evidence for B is itself evidence that A implies B. 

theorem andImpliesOr : A ∧ B →  A ∨ B := 
  fun andEvidence =>
    match andEvidence with
    | And.intro a b => Or.inl a

theorem onePlusOneAndLessThan : 1 + 1 = 2 ∨ 3 < 5 := by simp
theorem notTwoEqualFive : ¬(1 + 1 = 5) := by simp 
theorem trueisTure : True := True.intro
theorem trueOrFalse : True ∨ False := by simp
theorem falseImpliesTrue : False → True := by simp

-- Evidence as Arguments

-- def third (xs : List α) : α := xs[2]
-- failed to prove index is valid, possible solutions:
--   - Use `have`-expressions to prove the index is valid
--   - Use `a[i]!` notation instead, runtime check is perfomed, and 'Panic' error message is produced if index is not valid
--   - Use `a[i]?` notation instead, result is an `Option` type
--   - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
-- α : Type ?u.3900
-- xs : List α
-- ⊢ 2 < List.length xs

def third (xs : List α) (ok : xs.length > 2) : α := xs[2]
#eval third woodlandCritters (by simp)

-- Indexing Without Evidence
def thirdOption (xs : List α) : Option α := xs[2]?
#eval thirdOption woodlandCritters
#eval thirdOption ["only", "two"]

#eval woodlandCritters[1]!

-- def unsafeThird (xs : List α) : α := xs[2]!
-- failed to synthesize instance
--   Inhabited α

-- only programs whose types contain at least one value 
-- are allowed to crash.

-- #eval woodlandCritters [1]
-- function expected at
--   woodlandCritters
-- term has type
--   List String

-- wrong whitespace, 
-- Lean will treat woodlandCritters as a function

-- Exercise
-- 1
theorem th1 : 2 + 3 = 5 := rfl
theorem th2 : 15 - 8 = 7 := rfl 
theorem th3 : "Hello, ".append "world" = "Hello, world" := rfl
-- theorem th4 : 5 < 18 := rfl 

-- 2
theorem th1': 2 + 3 = 5 :=by simp
theorem th2': 15 - 8 = 7 :=by simp
theorem th3': "Hello, ".append "world" = "Hello, world" := by simp
theorem th4': 5 < 18 := by simp 

-- 3
def fifth (xs : List α) (ok : xs.length > 14): α := xs[14]
-- #eval fifth woodlandCritters (by simp)