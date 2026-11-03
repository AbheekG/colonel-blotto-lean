import Blotto.GeneralPaperEqualFirstPrefixRates

/-! Complete literal bit-preparation ledger for the actual paper boundary:
one c=256 rounding/length pass, one branch scan and exactly one continuation.
Every phase price is derived from executed routines. Calibration to the paper
asymptotic time/working-space headline remains a separate obligation. -/
namespace Blotto.GeneralPaperEqualFirstPreparationWork
open GeneralPaperEqualFirstRounding
open GeneralPaperEqualFiniteKernel (terminal)
open GeneralPaperEqualFirstPrefixRates
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def continuationBound (model : RationalCostModel) (A n k b : ℕ) : ℕ :=
  packingBound model A n k+routeBound model A n k+segmentBound model A n k+
    GeneralPaperEqualFirstClosureRates.bound model A n k b

theorem continuation_work {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1)
    (lengths : FixedArrayTable n ℚ)
    (hL : ∀ j, lengths.read j = (terminal (rounded true model W k values v hv) small).length j)
    (budget : ℚ) :
    (GeneralPaperEqualBitContinuation.run model A k (rounded true model W k values v hv) small lengths hL budget).2 ≤
      continuationBound model A n k (rationalWordWidth budget) := by
  let packed := GeneralPaperEqualMaterializedPacking.run (terminal (rounded true model W k values v hv) small)
    model A lengths hL (List.finRange n) (GeneralPaperEqualPreparationPrefix.uniform_items _ small).symm
  let routes := GeneralPaperEqualRouteConstruction.prepare packed.1 model A lengths hL
  let full := GeneralPaperEqualNativeSegmentPreparation.prepared (rounded true model W k values v hv) small packed.1 model A
  have hp := packing model W A k values v hv small lengths hL
  have hr := GeneralPaperEqualFirstPrefixRates.routes model W A k values v hv small packed.1 lengths hL
  have hs := segments model W A k values v hv small packed.1
  have hc := GeneralPaperEqualFirstClosureRates.work model W A k values v hv small routes.1 full.1
    packed.1.groups.data.size packed.1.groups.size budget
  change packed.2 ≤ _ at hp
  change routes.2 ≤ _ at hr
  change full.2 ≤ _ at hs
  dsimp only [packed, routes, full] at hp hr hs hc
  unfold GeneralPaperEqualBitContinuation.run continuationBound
  dsimp only
  omega

def bound {n : ℕ} (model : RationalCostModel) (W A k : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  prefixBound model W A k values+continuationBound model A n k (rationalWordWidth budget)+
    GeneralPaperEqualBitBranchRates.scanProfile model A n (k+1)+
    GeneralPaperEqualBitVertex.bound A n (rationalWordWidth budget)+192*A+192

theorem work {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) :
    (GeneralPaperEqualFirstBitDispatch.run model W A k values v hv budget).2 ≤ bound model W A k values budget := by
  let raw := GeneralPaperValueRoundingPaperContract.run true model W 256 k values
  let lengths := GeneralPaperEqualLengthArray.run model A raw.1.1 raw.1.2
  let r := rounded true model W k values v hv
  have hL : ∀ j, lengths.1.read j = 2*r.weight j := by
    intro j; rw [GeneralPaperEqualLengthArray.data, FixedArrayTable.read_ofFn]; rfl
  have hp := prefix_work model W A k values v hv
  have hWidth : ∀ j, rationalWordWidth (lengths.1.read j) ≤ 1+6*(binaryWordWidth n+k+12) := by
    dsimp only [lengths, raw]
    rw [source_successor]
    simpa only [Nat.add_assoc] using GeneralPaperEqualBitBoundaryScan.native_width model W A (k+1) values v hv
  have hs := GeneralPaperEqualBitBoundaryScan.run_work model A (1+6*(binaryWordWidth n+k+12)) lengths.1
    (by omega) hWidth
  have ht : ∀ small : ∀ j, 2*r.weight j ≤ 1,
      raw.2+lengths.2+(GeneralPaperEqualBitContinuation.run model A k r small lengths.1 hL budget).2 ≤
        prefixBound model W A k values+continuationBound model A n k (rationalWordWidth budget) :=
    fun small => Nat.add_le_add hp (continuation_work model W A k values v hv small lengths.1 hL budget)
  have hj := GeneralPaperEqualBitBranchRates.join model A k r budget lengths.1 hL (raw.2+lengths.2)
    (prefixBound model W A k values+continuationBound model A n k (rationalWordWidth budget))
    (GeneralPaperEqualBitBranchRates.scanProfile model A n (k+1))
    (hp.trans (Nat.le_add_right _ _)) (by simpa only [GeneralPaperEqualBitBranchRates.scanProfile, Nat.add_assoc] using hs) ht
  change raw.2+lengths.2+(GeneralPaperEqualBitBranch.prepare model A k r budget lengths.1 hL).2+128*A+128 ≤ _
  unfold bound
  omega

end Blotto.GeneralPaperEqualFirstPreparationWork
