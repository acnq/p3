-- 6.0 : Every monad is an applicative functor, and every applicative functor is a functor, but the converses do not hold.

-- 6.1 : Structures and Inheritances

structure MythicalCreature where
  large : Bool
deriving Repr

#check MythicalCreature.mk
#check MythicalCreature.large

structure Monster extends MythicalCreature where
  vulnerability : String
deriving Repr 

def troll : Monster where
  large := true
  vulnerability := "sunlight"

#check Monster.mk -- take MythicalCreature as construct arguments

#eval troll.toMythicalCreature -- unlike upcast in OOL, the other fields is erased

def troll2 : Monster := {large := true, vulnerability := "sunlight"}

-- def troll3 : Monster := ⟨true, "sunlight"⟩
-- application type mismatch
--   Monster.mk true
-- argument
--   true
-- has type
--   Bool : Type
-- but is expected to have type
--   MythicalCreature : Type
-- don't use angle-bracket notation directly
-- should be 
def troll3 : Monster := ⟨⟨true⟩, "sunlight"⟩

#eval troll.large -- OK
-- #eval MythicalCreature.large troll 
-- application type mismatch
--   troll.large
-- argument
--   troll
-- has type
--   Monster : Type
-- but is expected to have type
--   MythicalCreature : Type -- not OK, 
-- since it's typemismatch normal function call

def MythicalCreature.small (c : MythicalCreature) : Bool := !c.large
#eval troll.small
-- #eval MythicalCreature.small troll 
-- application type mismatch
--   MythicalCreature.small troll
-- argument
--   troll
-- has type
--   Monster : Type
-- but is expected to have type
--   MythicalCreature : Type -- same as above error

-- Multiple Inheritance
structure Helper extends MythicalCreature where
  assistance : String
  payment : String
deriving Repr 

def nisse : Helper where
  large := false
  assistance := "household tasks"
  payment := "porridge"

structure MonstrousAssistant extends Monster, Helper where
deriving Repr

def domesticatedTroll : MonstrousAssistant where
  large := false
  assistance := "heavy labor"
  payment := "toy goats"
  vulnerability := "sunlight"

#check MonstrousAssistant.mk

-- It takes a Monster as an argument, 
-- along with the two fields that Helper introduces on top of MythicalCreature.

-- Similarly, while MonstrousAssistant.toMonster merely extracts the Monster from the constructor,
-- MonstrousAssistant.toHelper has no Helper to extract. 

#print MonstrousAssistant.toHelper

-- Default Declarations
inductive Size where
  | small
  | medium
  | large
deriving BEq

structure SizedCreature extends MythicalCreature where
  size : Size
  large := size == Size.large 

def nonsenseCreature : SizedCreature where
  large := false
  size := .large -- default is just default, no check 

abbrev SizeMatch (sc : SizedCreature) : Prop := 
  sc.large = (sc.size == Size.large)

def huldre : SizedCreature where
  size := .medium

example : SizeMatch huldre := by  
  simp 
#eval huldre.large 

-- Type Class Inheritance
-- the same as structre, since behind the scenes, type classes are structures.
