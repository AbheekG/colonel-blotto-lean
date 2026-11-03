import Blotto.GeneralPaperComputedThreshold
import Blotto.RationalHeightSum
import Blotto.RationalExpressionWordWidth

/-! Actual rational DP resources grow with the number of merged fields.
No common O(A)-bit bound is asserted for all prefix sums. These certificates
cover retained cells and every successful candidate before minimum selection.
-/
namespace Blotto.GeneralPaperExactScoreDP
open GeneralPaperMinimum
set_option autoImplicit false
set_option maxHeartbeats 1000000

def CostHeight {K : ℕ} (fields : List (Field K)) (A : ℕ) : Prop :=
  ∀ field ∈ fields,∀ label,RationalHeight (field.read label).2 A

theorem fits_height {K : ℕ} (fields : List (Field K)) (A : ℕ) (hFields : CostHeight fields A)
    (s : ℕ) (chosen : Selection K) (h : Fits fields s chosen) :
    RationalHeight chosen.cost ((A+1)*fields.length+1) := by
  induction fields generalizing s chosen with
  | nil =>
    rw [h.2]
    norm_num [RationalHeight]
  | cons field rest ih =>
    obtain ⟨label,_,tail,hTail,rfl⟩ := h
    have hc := hFields field (by simp) label
    have ht := ih (fun f hf => hFields f (by simp [hf])) _ _ hTail
    have ha := hc.add ht
    change RationalHeight ((field.read label).2+tail.cost) _
    exact ha.mono (by simp only [List.length_cons,Nat.mul_add,Nat.mul_one]; omega)

theorem run_some_height {K : ℕ} (S : ℕ) (fields : List (Field K)) (A : ℕ) (hFields : CostHeight fields A)
    (s : Fin (S+1)) (chosen : Selection K) (h : (run S fields).read s=some chosen) :
    RationalHeight chosen.cost ((A+1)*fields.length+1) := by
  have hb := run_best S fields s
  rw [h] at hb
  exact fits_height fields A hFields s.val chosen hb.1

theorem run_some_width {K : ℕ} (S : ℕ) (fields : List (Field K)) (A : ℕ) (hFields : CostHeight fields A)
    (s : Fin (S+1)) (chosen : Selection K) (h : (run S fields).read s=some chosen) :
    rationalWordWidth chosen.cost ≤ 1+2*((A+1)*fields.length+1) :=
  rationalWordWidth_of_height (run_some_height S fields A hFields s chosen h)

theorem candidate_some_fits {K S : ℕ} (field : Field K) (rest : List (Field K))
    (s : Fin (S+1)) (label : Fin K) (chosen : Selection K)
    (h : candidate field (run S rest) s label=some chosen) : Fits (field::rest) s.val chosen := by
  have hb := candidate_best field rest (run S rest) (fun s => run_best S rest s) s label
  rw [h] at hb
  exact ⟨label,hb.1⟩

theorem candidate_some_height {K S : ℕ} (field : Field K) (rest : List (Field K)) (A : ℕ)
    (hFields : CostHeight (field::rest) A) (s : Fin (S+1)) (label : Fin K) (chosen : Selection K)
    (h : candidate field (run S rest) s label=some chosen) :
    RationalHeight chosen.cost ((A+1)*(rest.length+1)+1) :=
  fits_height (field::rest) A hFields s.val chosen (candidate_some_fits field rest s label chosen h)

end Blotto.GeneralPaperExactScoreDP
