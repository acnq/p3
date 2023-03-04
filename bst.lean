inductive Tree (β : Type v) where
  | leaf
  | node (left : Tree β) (key : Nat) (value : β) (right : Tree β)
deriving Repr

def Tree.contains(t : Tree β) (k: Nat) : Bool :=
  match t with
  | leaf => false
  | node left key value right =>
    if k < key then 
      left.contains k
    else if key < k then 
      right.contains k
    else
      true 

def Tree.find? (t : Tree β) (k : Nat): Option β :=
  match t with
  | leaf => none
  | node left key value right =>
    if k < key then 
      left.find? k
    else if key < k then 
      right.find? k
    else
      some value

def Tree.insert (t : Tree β) (k : Nat) (v : β) : Tree β :=
  match t with
  | leaf => node leaf k v leaf
  | node left key value right =>
    if k < key then 
      node (left.insert k v) key value right
    else if key < k then
      node left key value (right.insert k v)
    else 
      node left k v right

def Tree.toList (t : Tree β) : List (Nat × β) :=
  match t with
  | leaf => []
  | node l k v r => l.toList ++ [(k, v)] ++ r.toList

#eval Tree.leaf.insert 2 "two"
  |>.insert 3 "three"
  |>.insert 1 "one"

#eval Tree.leaf.insert 2 "two"
  |>.insert 3 "three"
  |>.insert 1 "one"
  |>.toList