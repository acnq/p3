-- Programming with Dependent Types 
-- Dependent types are types that contain non-type expressions. 

def natOrStringThree (b : Bool) : if b then Nat else String := 
  match b with
  | true => (3 : Nat)
  | false => "three"