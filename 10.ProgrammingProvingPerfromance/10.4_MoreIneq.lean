-- More Inequalities

-- Merge Sort
def merge [Ord α] (xs : List α) (ys : List α) : List α := 
  match xs, ys with 
  | [], _ => ys 
  | _, [] => xs 
  | x'::xs', y'::ys' =>
    match Ord.compare x' y' with 
      | .lt | .eq => x' :: merge xs' (y' :: ys')
      | .gt => y' :: merge (x'::xs') ys'
termination_by merge xs ys => xs.length + ys.length 

def merge2 [Ord α] (xs : List α) (ys : List α) : List α := 
  match xs, ys with 
  | [], _ => ys 
  | _, [] => xs 
  | x'::xs', y'::ys' =>
    match Ord.compare x' y' with 
      | .lt | .eq => x' :: merge2 xs' (y' :: ys')
      | .gt => y' :: merge2 (x'::xs') ys'
termination_by merge2 xs ys => (xs, ys)



def splitList (lst : List α) : (List α × List α) :=
  match lst with 
  | [] => ([], [])
  | x :: xs =>
    let (a, b) := splitList xs 
    (x :: b, a)


-- Splitting a List Makes it Shorter
namespace Hidden 
structure And (a b : Prop) : Prop where 
  intro ::
  left : a
  right : b
end Hidden 

-- Adding One to Both Sides
namespace Hidden 
theorem Nat.succ_le_succ : n ≤ m → Nat.succ n ≤ Nat.succ m := by 
  intro h 
  induction h with 
  | refl => constructor 
  | step h' ih => 
    constructor 
    assumption 
theorem Nat.succ_le_succ2 : n ≤ m → Nat.succ n ≤ Nat.succ m
  | .refl => .refl 
  | .step h' => .step (Nat.succ_le_succ2 h')


-- Adding One to the Greater Side 
theorem Nat.le_succ_of_le : n ≤ m → n ≤ Nat.succ m := by 
  intro h 
  induction h with 
  | refl => constructor; constructor 
  | step => constructor; assumption  

theorem Nat.le_succ_of_le2 : n ≤ m → n ≤ Nat.succ m := by 
  intro h 
  induction h with 
  | refl => apply Nat.le.step; exact Nat.le.refl
  | step _ ih => apply Nat.le.step; exact ih 

theorem Nat.le_succ_of_le3 (h : n ≤ m ) : n ≤ Nat.succ m := by 
  induction h <;> repeat (first | constructor | assumption)

theorem Nat.le_succ_of_le4 : n ≤ m → n ≤ Nat.succ m 
  | .refl => .step .refl
  | .step h => .step (Nat.le_succ_of_le4 h) 

end Hidden 

-- Finishing the Proof 
theorem splitList_shorter_le (lst : List α) : 
  (splitList lst).fst.length ≤ lst.length ∧
    (splitList lst).snd.length ≤ lst.length := by
  induction lst with 
  | nil => simp [splitList]
  | cons x xs ih => 
    simp [splitList]
    cases ih 
    constructor 
    case left => apply Nat.succ_le_succ; assumption
    case right => apply Nat.le_succ_of_le; assumption 

theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) : 
  (splitList lst).fst.length < lst.length ∧ 
    (splitList lst).snd.length < lst.length := by 
  match lst with
  | x :: y :: xs => 
    simp_arith [splitList]
    apply splitList_shorter_le

theorem splitList_shorter_fst (lst : List α) (h : lst.length ≥ 2) : 
    (splitList lst).fst.length < lst.length :=
  splitList_shorter lst h |>.left

theorem splitList_shorter_snd (lst : List α) (h : lst.length ≥ 2) : 
    (splitList lst).snd.length < lst.length :=
  splitList_shorter lst h |>.right

-- Merge Sort Terminates
def mergeSort [Ord α] (xs : List α) : List α := 
  if h : xs.length < 2 then 
    match xs with
    | [] => []
    | [x] => [x]
  else 
    let halves := splitList xs 
    have : xs.length ≥ 2 := by   -- `have` is like `let` without names
      apply Nat.ge_of_not_lt
      assumption
    have : halves.fst.length < xs.length := by 
      apply splitList_shorter_fst
      assumption
    have : halves.snd.length < xs.length := by 
      apply splitList_shorter_snd
      assumption
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by mergeSort xs => xs.length 

#eval mergeSort [5, 3, 22, 15]

-- Division as Iterated Subtraction 
def div' (n k : Nat) (ok : k > 0) : Nat := 
  if h: n < k then 
    0
  else 
    have : 0 < n := by 
      cases n with 
      | zero => contradiction 
      | succ n' => simp_arith
    have : n - k < n := by
      apply Nat.sub_lt <;> assumption 
    1 + div' (n - k) k ok 
termination_by div' n k ok => n 