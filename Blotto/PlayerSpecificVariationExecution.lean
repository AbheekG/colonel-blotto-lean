import Blotto.PlayerSpecificHornerTraceCost

/-! Executable zero-skipping sign-variation counting with actual rational
comparison/copy/control traces. Its numerical result equals the library
counter used by the verified Sturm computation. -/
namespace Blotto.PlayerSpecificVariationExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 4000000

def frame (row : Data) (a b : ℚ) : Trace :=
  copyRow row++(equalZero a).2++(equalZero b).2++
    [.compare a 0,.compare 0 a,.compare b 0,.compare 0 b,.control row.length]

def assemble (pre : Trace) (rest : ℕ×Trace) (increment : ℕ) : ℕ×Trace :=
  (rest.1+increment,pre++rest.2++[.control rest.1,.control increment,.control (rest.1+increment)])

def run (row : Data) : ℕ×Trace :=
  match row with
  | [] => (0,[.control 0])
  | [a] => (0,copyRow [a]++(equalZero a).2++[.control 0])
  | a::b::rest =>
    let pre := frame (a::b::rest) a b
    if a=0 then assemble pre (run (b::rest)) 0 else
    if b=0 then assemble pre (run (a::rest)) 0 else
      assemble pre (run (b::rest)) (if SignType.sign a=SignType.sign b then 0 else 1)
termination_by row.length
decreasing_by all_goals simp only [List.length_cons]; omega

theorem value (row : Data) : (run row).1=row.signVariations := by
  induction hn : row.length using Nat.strong_induction_on generalizing row with
  | h n ih =>
    cases row with
    | nil => rw [run.eq_def]; rfl
    | cons a tail =>
      cases tail with
      | nil => rw [run.eq_def]; exact (List.signVariations_singleton a).symm
      | cons b rest =>
        have hlen : rest.length+2=n := by simpa only [List.length_cons,Nat.add_assoc] using hn
        rw [run.eq_def]
        dsimp only
        by_cases ha : a=0
        · rw [ite_eq_left ha]
          change (run (b::rest)).1+0=(a::b::rest).signVariations
          rw [Nat.add_zero,ih (rest.length+1) (by omega) (b::rest) rfl,ha,List.signVariations_zero_cons]
        · rw [ite_eq_right ha]
          by_cases hb : b=0
          · rw [ite_eq_left hb]
            change (run (a::rest)).1+0=(a::b::rest).signVariations
            rw [Nat.add_zero,ih (rest.length+1) (by omega) (a::rest) rfl,hb,List.signVariations_cons_zero_cons]
          · rw [ite_eq_right hb]
            change (run (b::rest)).1+_= _
            rw [ih (rest.length+1) (by omega) (b::rest) rfl,List.signVariations_cons_cons_of_ne_zero rest ha hb]

theorem count_le_length (row : Data) : (run row).1≤row.length := by
  induction hn : row.length using Nat.strong_induction_on generalizing row with
  | h n ih =>
    cases row with
    | nil => rw [run.eq_def]; dsimp only; omega
    | cons a tail =>
      cases tail with
      | nil => rw [run.eq_def]; dsimp only; omega
      | cons b rest =>
        have hlen : rest.length+2=n := by simpa only [List.length_cons,Nat.add_assoc] using hn
        have hl := ih (rest.length+1) (by omega) (b::rest) rfl
        have hr := ih (rest.length+1) (by omega) (a::rest) rfl
        rw [run.eq_def]
        dsimp only
        split_ifs <;> dsimp only [assemble] <;> omega

theorem frame_length (row : Data) (a b : ℚ) : (frame row a b).length=row.length+12 := by
  simp only [frame,List.length_append,copyRow_length,equalZero_length,List.length_cons,List.length_nil]

theorem trace_length (row : Data) : (run row).2.length≤20*(row.length+1)^2 := by
  induction hn : row.length using Nat.strong_induction_on generalizing row with
  | h n ih =>
    cases row with
    | nil => rw [run.eq_def]; norm_num; nlinarith
    | cons a tail =>
      cases tail with
      | nil =>
        rw [run.eq_def]
        simp only [List.length_append,copyRow_length,equalZero_length,List.length_cons,List.length_nil]
        nlinarith
      | cons b rest =>
        have hlen : rest.length+2=n := by simpa only [List.length_cons,Nat.add_assoc] using hn
        have hl := ih (rest.length+1) (by omega) (b::rest) rfl
        have hr := ih (rest.length+1) (by omega) (a::rest) rfl
        rw [run.eq_def]
        dsimp only
        split_ifs <;> dsimp only [assemble] <;>
          simp only [List.length_append,frame_length,List.length_cons,List.length_nil] at hl hr ⊢ <;> nlinarith

end Blotto.PlayerSpecificVariationExecution
