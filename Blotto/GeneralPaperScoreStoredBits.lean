import Blotto.GeneralPaperScorePreparationWork

/-! Conservative logical description sizes of actual stored score cells.
Each cell has one rational resource. A predecessor node contains a label
and references, not another copy of the rational resource. Counting shared
label tails separately in every cell is a safe upper bound. Simultaneous
evaluator storage requires the separate prefix/temporary/frame join.
-/
namespace Blotto.GeneralPaperScoreStoredBits
open GeneralPaperMinimum GeneralPaperExactScoreDP
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000

def cellBits {K : ℕ} (W : ℕ) : Option (Selection K) → ℕ
  | none => 2*W+2
  | some chosen => rationalWordWidth chosen.cost+4*W+4+chosen.labels.length*(binaryWordWidth K+2*W+4)

def cellBound (K W A r : ℕ) : ℕ :=
  1+2*((A+1)*r+1)+4*W+4+r*(binaryWordWidth K+2*W+4)

def tableBits {K S : ℕ} (W : ℕ) (table : FixedArrayTable (S+1) (Option (Selection K))) : ℕ :=
  4*W+4+(S+1)*W+∑ s,cellBits W (table.read s)

theorem cellBound_mono (K W A : ℕ) {r t : ℕ} (hrt : r≤t) : cellBound K W A r≤cellBound K W A t := by
  have h1 := Nat.mul_le_mul_left (A+1) hrt
  have h2 := Nat.mul_le_mul_right (binaryWordWidth K+2*W+4) hrt
  unfold cellBound
  omega

theorem none_bits (K W A r : ℕ) : cellBits (K:=K) W none≤cellBound K W A r := by
  simp only [cellBits,cellBound]
  omega

theorem fits_bits {K : ℕ} (fields : List (Field K)) (W A s : ℕ) (chosen : Selection K)
    (hFields : CostHeight fields A) (hFits : Fits fields s chosen) :
    cellBits W (some chosen)≤cellBound K W A fields.length := by
  have hWidth := rationalWordWidth_of_height (fits_height fields A hFields s chosen hFits)
  have hLength := fits_length fields s chosen hFits
  simp only [cellBits,cellBound,hLength]
  omega

theorem run_cell_bits {K : ℕ} (fields : List (Field K)) (W A S : ℕ) (hFields : CostHeight fields A)
    (s : Fin (S+1)) : cellBits W ((run S fields).read s)≤cellBound K W A fields.length := by
  have h := run_best S fields s
  cases he : (run S fields).read s with
  | none => exact none_bits K W A fields.length
  | some chosen =>
    rw [he] at h
    exact fits_bits fields W A s.val chosen hFields h.1

theorem run_table_bits {K : ℕ} (fields : List (Field K)) (W A S : ℕ) (hFields : CostHeight fields A) :
    tableBits W (run S fields)≤4*W+4+(S+1)*(W+cellBound K W A fields.length) := by
  have h := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => run_cell_bits fields W A S hFields s)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at h
  unfold tableBits
  nlinarith only [h]

theorem candidate_bits {K S : ℕ} (field : Field K) (rest : List (Field K)) (W A : ℕ)
    (hFields : CostHeight (field::rest) A) (s : Fin (S+1)) (l : Fin K) :
    cellBits W (candidate field (run S rest) s l)≤cellBound K W A (rest.length+1) := by
  cases he : candidate field (run S rest) s l with
  | none => exact none_bits K W A (rest.length+1)
  | some chosen =>
    exact fits_bits (field::rest) W A s.val chosen hFields (candidate_some_fits field rest s l chosen he)

theorem candidate_batch_bits {K S : ℕ} (field : Field K) (rest : List (Field K)) (W A : ℕ)
    (hFields : CostHeight (field::rest) A) (s : Fin (S+1)) :
    (∑ l : Fin K,cellBits W (candidate field (run S rest) s l))≤K*cellBound K W A (rest.length+1) := by
  have h := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => candidate_bits field rest W A hFields s l)
  simpa only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] using h

end Blotto.GeneralPaperScoreStoredBits
