import Blotto.GeneralPaperPreparedScoreBits

/-! The actual array fill's every prefix, with the previous stored layer
and the candidate scan's whole batch. These bound simultaneous numerical
and predecessor data during a layer. Input matrices, source control frames,
reference-address capacity and other phases still need the full space join.
-/
namespace Blotto.GeneralPaperScorePrefixBits
open GeneralPaperMinimum GeneralPaperExactScoreDP GeneralPaperScoreStoredBits
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000

def prefixArray {K S : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K)
    (previous : FixedArrayTable (S+1) (Option (Selection K))) (k : ℕ) (hk : k≤S+1) : Array (Option (Selection K)) :=
  (PaperIndexedArrayConstruction.fill (fun w => w) W
    (fun s => GeneralPaperScoreBitPrimitive.scanRun model W
      (GeneralPaperScoreBitPrimitive.candidateRun model W field previous s) (List.finRange K)) k hk).1

theorem prefix_data {K S : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K)
    (previous : FixedArrayTable (S+1) (Option (Selection K))) (k : ℕ) (hk : k≤S+1) :
    prefixArray model W field previous k hk=Array.ofFn (fun i : Fin k =>
      (step field previous).read ⟨i.val,lt_of_lt_of_le i.isLt hk⟩) := by
  unfold prefixArray
  rw [PaperIndexedArrayConstruction.fill_data]
  congr 1
  funext i
  simp only [GeneralPaperScoreBitPrimitive.scan_data,GeneralPaperScoreBitPrimitive.candidate_data,
    step,FixedArrayTable.read_ofFn]

def arrayBits {K : ℕ} (W : ℕ) (a : Array (Option (Selection K))) : ℕ :=
  4*W+4+a.size*W+(a.toList.map (cellBits W)).sum

theorem prefix_bits {K S : ℕ} (model : RationalCostModel) (W A : ℕ) (field : Field K) (rest : List (Field K))
    (hFields : CostHeight (field::rest) A) (k : ℕ) (hk : k≤S+1) :
    arrayBits W (prefixArray model W field (run S rest) k hk)≤
      4*W+4+k*(W+cellBound K W A (rest.length+1)) := by
  have hEach (i : Fin k) :
      cellBits W ((step field (run S rest)).read ⟨i.val,lt_of_lt_of_le i.isLt hk⟩)≤
        cellBound K W A (rest.length+1) :=
    run_cell_bits (field::rest) W A S hFields ⟨i.val,lt_of_lt_of_le i.isLt hk⟩
  have hSum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hEach i)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hSum
  unfold arrayBits
  rw [prefix_data]
  simp only [Array.size_ofFn,Array.toList_ofFn,List.map_ofFn,Function.comp_def,List.sum_ofFn]
  nlinarith only [hSum]

def liveData {K S : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K) (rest : List (Field K))
    (k : ℕ) (hk : k≤S+1) (s : Fin (S+1)) : ℕ :=
  tableBits W (run S rest)+arrayBits W (prefixArray model W field (run S rest) k hk)+
    ∑ l : Fin K,cellBits W (candidate field (run S rest) s l)

def profile (K S W A r : ℕ) : ℕ :=
  2*(4*W+4+(S+1)*(W+cellBound K W A r))+K*cellBound K W A r

theorem liveData_bound {K S : ℕ} (model : RationalCostModel) (W A : ℕ) (field : Field K) (rest : List (Field K))
    (hFields : CostHeight (field::rest) A) (k : ℕ) (hk : k≤S+1) (s : Fin (S+1)) :
    liveData model W field rest k hk s≤profile K S W A (rest.length+1) := by
  have hp := run_table_bits rest W A S (fun f hf => hFields f (by simp [hf]))
  have hm := cellBound_mono K W A (Nat.le_succ rest.length)
  have hp' := hp.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_left (S+1) (Nat.add_le_add_left hm W)) (4*W+4))
  have hc := prefix_bits model W A field rest hFields k hk
  have hc' := hc.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right (W+cellBound K W A (rest.length+1)) hk) (4*W+4))
  have hb := candidate_batch_bits field rest W A hFields s
  simp only [Nat.succ_eq_add_one] at hp'
  unfold liveData profile
  omega

end Blotto.GeneralPaperScorePrefixBits
