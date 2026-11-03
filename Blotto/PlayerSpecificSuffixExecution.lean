import Blotto.PlayerSpecificRationalMaximumExecution

/-! Executed cached suffix maxima with full input/head/output record
copies. Numeric values refine the existing single-backwards-pass suffix
construction; this source trace also includes complete returned lists. -/
namespace Blotto.PlayerSpecificSuffixExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

abbrev Rows := List ((ℚ×ℚ)×ℚ)
def copyRows (rows : Rows) : Trace :=
  [.control rows.length]++rows.flatMap (fun x => copyRow [x.1.1,x.1.2,x.2])
def run : List (ℚ×ℚ) → (ℚ×Rows)×Trace
  | [] => ((0,[]),copyRow [0]++copyRows []++[.control 0])
  | x::xs =>
    let tail:=run xs
    let maximum:=PlayerSpecificRationalMaximumExecution.run x.2 tail.1.1
    let rows:=(x,maximum.1)::tail.1.2
    ((maximum.1,rows),tail.2++maximum.2++copyRow [x.1,x.2]++copyRow [maximum.1]++copyRows rows++[.control rows.length])

theorem values (fields : List (ℚ×ℚ)) :
    (run fields).1.1=(PlayerSpecificSweepBounds.suffixes fields).1 ∧
      (run fields).1.2=(PlayerSpecificSweepBounds.suffixes fields).2.1 := by
  induction fields with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    simp only [run,PlayerSpecificRationalMaximumExecution.value,ih.1,ih.2,PlayerSpecificSweepBounds.suffixes,and_self]

theorem rows_length (fields : List (ℚ×ℚ)) : (run fields).1.2.length=fields.length := by
  rw [(values fields).2]
  have h:=congrArg List.length (PlayerSpecificSweepBounds.suffixes_fields fields)
  simpa only [List.length_map] using h

theorem copy_rows_length (rows : Rows) : (copyRows rows).length=4*rows.length+1 := by
  simp only [copyRows,List.length_append,List.length_cons,List.length_nil,List.length_flatMap]
  induction rows with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,copyRow_length,List.length_cons,List.length_nil] at ih ⊢
    omega

theorem trace_length (fields : List (ℚ×ℚ)) : (run fields).2.length≤100*(fields.length+1)^2 := by
  induction fields with
  | nil => decide
  | cons x xs ih =>
    simp only [run,List.length_append,PlayerSpecificRationalMaximumExecution.length,copyRow_length,
      copy_rows_length,rows_length,List.length_cons,List.length_nil] at ih ⊢
    nlinarith only [ih]

end Blotto.PlayerSpecificSuffixExecution
