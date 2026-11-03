import Blotto.GeneralPaperQuantileComparison

/-! A descent stores one direction per level. Its final code is computed by
one linear multiply-by-two fold. Powers below are reference semantics only.
-/
namespace Blotto.GeneralPaperQuantilePath
set_option autoImplicit false

def index : List Bool → ℕ
  | [] => 0
  | bit::tail => (if bit then 2^tail.length else 0)+index tail

def encode (path : List Bool) : ℕ := path.foldl (fun acc bit => 2*acc+if bit then 1 else 0) 0

theorem fold_index (path : List Bool) (acc : ℕ) :
    path.foldl (fun acc bit => 2*acc+if bit then 1 else 0) acc=acc*2^path.length+index path := by
  induction path generalizing acc with
  | nil => simp [index]
  | cons bit tail ih =>
    rw [List.foldl_cons,ih]
    cases bit <;> simp only [List.length_cons,index,Bool.false_eq_true,ite_false,ite_true,pow_succ] <;> ring

theorem encode_index (path : List Bool) : encode path=index path := by
  simpa only [encode,Nat.zero_mul,Nat.zero_add] using fold_index path 0

theorem index_bound (path : List Bool) : index path<2^path.length := by
  induction path with
  | nil => simp [index]
  | cons bit tail ih =>
    cases bit <;> simp only [index,List.length_cons,pow_succ,Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem left_index (path : List Bool) : index (false::path)=index path := by simp [index]

theorem right_index (path : List Bool) : index (true::path)=2^path.length+index path := by simp [index]

end Blotto.GeneralPaperQuantilePath
