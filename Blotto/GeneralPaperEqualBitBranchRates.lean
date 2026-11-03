import Blotto.GeneralPaperEqualBitBranch

/-! Compose the already-paid prefix with exactly one selected bit branch.
The generic join is arithmetic on measured prices; the concrete native
caller supplies prefix/continuation bounds from actual source calls. -/
namespace Blotto.GeneralPaperEqualBitBranchRates
open GeneralPaperEqualFiniteKernel (terminal)
set_option autoImplicit false
set_option maxHeartbeats 2400000

def scanProfile (model : RationalCostModel) (A n k : ℕ) : ℕ :=
  n * GeneralPaperEqualBitBoundaryScan.stepBound model A n (1 + 6 * (binaryWordWidth n + k + 11)) +
    GeneralPaperEqualRouteConstruction.indicesWork A n + 96 * A + 96

theorem join {n : ℕ} (model : RationalCostModel) (A k : ℕ) (v : RationalFieldSelector n) (budget : ℚ)
    (lengths : FixedArrayTable n ℚ) (hL : ∀ j, lengths.read j = 2 * v.weight j)
    (prefixPrice fullPrice scanPrice : ℕ)
    (hp : prefixPrice ≤ fullPrice)
    (hs : (GeneralPaperEqualBitBoundaryScan.run model A lengths).2 ≤ scanPrice)
    (ht : ∀ small : ∀ j, 2 * v.weight j ≤ 1,
      prefixPrice + (GeneralPaperEqualBitContinuation.run model A k v small lengths hL budget).2 ≤ fullPrice) :
    prefixPrice + (GeneralPaperEqualBitBranch.prepare model A k v budget lengths hL).2 ≤
      fullPrice + scanPrice + GeneralPaperEqualBitVertex.bound A n (rationalWordWidth budget) + 64 * A + 64 := by
  unfold GeneralPaperEqualBitBranch.prepare
  dsimp only
  split
  · rename_i chosen h
    have hv := GeneralPaperEqualBitVertex.work A budget chosen
    omega
  · rename_i h
    have hx := ht (GeneralPaperEqualRealBoundaryScan.none_small lengths v hL
      ((GeneralPaperEqualBitBoundaryScan.run_data model A lengths).symm.trans h))
    omega

def prefixProfile {n : ℕ} (model : RationalCostModel) (W A k : ℕ) (values : FixedArrayTable n ℚ) : ℕ :=
  (GeneralPaperValueRoundingPaperContract.scaleBitProfile model W 128 n k +
    13 * model.rat (GeneralPaperValueRoundingInputPrice.size (GeneralPaperValueRoundingPaperContract.scale 128 n k) values) +
    512 * (n + 1) * GeneralPaperSummaryArrayExecution.arrayWord W n + 128 * W) +
  ((12 * n + 2) * model.rat (1 + 2 * GeneralPaperEqualLengthArray.height (binaryWordWidth n + k + 11)) +
    64 * (n + 1) * (A + 1) + PaperIndexedArrayConstruction.overhead id A n n)

theorem prefix_le {n : ℕ} (model : RationalCostModel) (W A k : ℕ) (values : FixedArrayTable n ℚ) (b : ℕ) :
    prefixProfile model W A k values ≤ GeneralPaperEqualBitPreparationLedger.profile model W A k values b := by
  unfold prefixProfile GeneralPaperEqualBitPreparationLedger.profile
  dsimp only
  omega

theorem prefix_work {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :
    let raw := GeneralPaperValueRoundingPaperContract.run true model W 128 k values
    let lengths := GeneralPaperEqualLengthArray.run model A raw.1.1 raw.1.2
    raw.2 + lengths.2 ≤ prefixProfile model W A k values := by
  let raw := GeneralPaperValueRoundingPaperContract.run true model W 128 k values
  have hr := GeneralPaperValueRoundingPaperContract.bit_work model W 128 k values v hv
  have hD : binaryWordWidth raw.1.2 ≤ binaryWordWidth n + k + 11 :=
    (GeneralPaperEqualNativeSampler.roundDen_word true model W k values v hv).trans (by omega)
  have ha (j : Fin n) : raw.1.1.read j ≤ raw.1.2 :=
    (Finset.single_le_sum (s := Finset.univ) (f := fun i => raw.1.1.read i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans_eq
      (GeneralPaperValueRoundingPaperContract.source_sum true model W 128 k values)
  have hl := GeneralPaperEqualLengthArray.work model A raw.1.1 raw.1.2 (binaryWordWidth n + k + 11) (by omega) hD ha
  exact Nat.add_le_add hr hl

end Blotto.GeneralPaperEqualBitBranchRates
