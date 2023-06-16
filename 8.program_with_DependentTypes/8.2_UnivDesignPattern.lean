-- The Universe Design Pattern

-- Universe : also used for design pattern 
-- in which a datatype is used to represent aa subset of Lean's types
-- and function converts the datatype's constructors into actual types
-- values of this datatype are called `codes` for their types

-- Types directly describe other types are called *universe a la Russelll*
-- user defined universe represents all of their types as *data*, 
-- and include an explicit function to interpret these code into actul types
-- this arrangement is called *universe a la Tarsk*

inductive NatOrBool where
  | nat | bool 

abbrev NatOrBool.asType (code : NatOrBool) : Type := 
  match code with 
    | .nat => Nat 
    | .bool => Bool 

def decode (t : NatOrBool) (input : String) : Option t.asType := 
  match t with 
    | .nat => input.toNat?
    | .bool => 
      match input with 
        | "true" => some true 
        | "false" => some false 
        | _ => none 

inductive NestedPairs where 
  | nat : NestedPairs
  | pair : NestedPairs → NestedPairs → NestedPairs

abbrev NestedPairs.asType : NestedPairs → Type 
  | .nat => Nat 
  | .pair t1 t2 => asType t1 × asType t2 

-- type class search does not automatically 
-- check every possible case of a datatype 
-- in an instance declaration, 
-- because there might be infinitely many such cases

-- instance {t : NestedPairs} : BEq t.asType where 
--   beq x y := x == y 
-- failed to synthesize instance
--   BEq (NestedPairs.asType t)


def NestedPairs.beq (t : NestedPairs) (x y : t.asType) : Bool := 
  match t with 
  | .nat => x == y 
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd

-- Type Classes vs Universe 
-- Type classes allow an open-ended collection of types to be used with an API
-- as long as they've implementations

-- universe a la Tarksi, 
-- restricts the API to be usable only with a predetermined collection of types

-- A Universe of Finite Types 
-- restricted types enabe operations that'd be impossilbe for an open-ended API
-- e.g comparation of function equality 

inductive Finite where
  | unit : Finite
  | bool : Finite
  | pair : Finite → Finite → Finite
  | arr : Finite → Finite → Finite

abbrev Finite.asType : Finite → Type
  | .unit => Unit
  | .bool => Bool
  | .pair t1 t2 => asType t1 × asType t2
  | .arr t1 t2 => asType t1 → asType t2  -- function type 

def List.product (xs : List α) (ys : List β) : List (α × β) := Id.run do 
  let mut out : List (α × β) := []
  for x in xs do 
    for y in ys do 
      out := (x, y) :: out 
  pure out.reverse

namespace Hidden 
def List.foldr (f : α → β → β) (default : β) : List α → β 
  | []      => default
  | a :: l  => f a (foldr f default l)
end Hidden 


mutual 
  def Finite.enumerate (t : Finite) : List t.asType := 
    match t with 
    | .unit => [()]
    | .bool => [true, false]
    | .pair t1 t2 => t1.enumerate.product t2.enumerate
    | .arr t1 t2 => t1.functions t2.enumerate

def Finite.functions (t : Finite) (results : List α) : List (t.asType → α) := 
  match t with 
  | .unit => 
    results.map fun r => 
      fun () => r 
  | .bool => 
    (results.product results).map fun (r1, r2) => 
      fun 
        | true => r1 
        | false => r2 
  | .pair t1 t2 => 
    let f1s := t1.functions <| t2.functions results 
    f1s.map fun f => 
      fun (x, y) => 
        f x y 
  | .arr t1 t2 => 
    let args := t1.enumerate 
    let base := 
      results.map fun r => 
        fun _ => r 
    args.foldr 
      (fun arg rest => 
        (t2.functions rest).map fun more => 
          fun f => more (f arg) f)
        base
end 

def Finite.beq (t : Finite) (x y : t.asType) : Bool :=
  match t with
  | .unit => true
  | .bool => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd
  | .arr t1 t2 =>
    t1.enumerate.all fun arg => beq t2 (x arg) (y arg)

    
#eval Finite.beq (.arr .bool .bool) (fun _ => true) (fun b => b == b)
#eval Finite.beq (.arr .bool .bool) (fun _ => true) not 
#eval Finite.beq (.arr .bool .bool) id (not ∘ not)