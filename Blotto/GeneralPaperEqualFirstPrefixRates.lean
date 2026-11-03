import Blotto.GeneralPaperEqualFirstClosureRates

/-! Actual first-rounding and retained-length source prices, followed by
packing, routes and segments on those same arrays. Source-only successor
identification transfers the short bounds without changing draw precision. -/
namespace Blotto.GeneralPaperEqualFirstPrefixRates
open GeneralPaperEqualFirstRounding
open GeneralPaperEqualFiniteKernel (terminal lottery)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def prefixBound {n : ℕ} (model : RationalCostModel) (W A k : ℕ) (values : FixedArrayTable n ℚ) : ℕ :=
  (GeneralPaperValueRoundingPaperContract.scaleBitProfile model W 256 n k+
    13*model.rat (GeneralPaperValueRoundingInputPrice.size (GeneralPaperValueRoundingPaperContract.scale 256 n k) values)+
    512*(n+1)*GeneralPaperSummaryArrayExecution.arrayWord W n+128*W)+
  ((12*n+2)*model.rat (1+2*GeneralPaperEqualLengthArray.height (binaryWordWidth n+k+12))+
    64*(n+1)*(A+1)+PaperIndexedArrayConstruction.overhead id A n n)

def packingBound (model : RationalCostModel) (A n k : ℕ) : ℕ :=
  (12*n+12)*model.rat (3+2*(binaryWordWidth n+k+10))+(12*n+24)*A+
    GeneralPaperEqualPackingExecution.unit A n*(2*n+4)

def routeBound (model : RationalCostModel) (A n k : ℕ) : ℕ :=
  64*(n+1)*model.rat (4*(binaryWordWidth n+k+10)+3)+
    4096*(n+1)*(A+binaryWordWidth (n+1)+1)

def segmentBound (model : RationalCostModel) (A n k : ℕ) : ℕ :=
  4294967296*(model.rat (4194304*(binaryWordWidth n+k+11))+A+1)

theorem prefix_work {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :
    let raw := GeneralPaperValueRoundingPaperContract.run true model W 256 k values
    let lengths := GeneralPaperEqualLengthArray.run model A raw.1.1 raw.1.2
    raw.2+lengths.2 ≤ prefixBound model W A k values := by
  let raw := GeneralPaperValueRoundingPaperContract.run true model W 256 k values
  have hr := GeneralPaperValueRoundingPaperContract.bit_work model W 256 k values v hv
  have hD : binaryWordWidth raw.1.2 ≤ binaryWordWidth n+k+12 :=
    (denominator_word true model W k values v hv).trans (by omega)
  have ha (j : Fin n) : raw.1.1.read j ≤ raw.1.2 :=
    (Finset.single_le_sum (s := Finset.univ) (f := fun i => raw.1.1.read i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)).trans_eq (GeneralPaperValueRoundingPaperContract.source_sum true model W 256 k values)
  have hl := GeneralPaperEqualLengthArray.work model A raw.1.1 raw.1.2 (binaryWordWidth n+k+12) (by omega) hD ha
  exact Nat.add_le_add hr hl

theorem packing {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1)
    (lengths : FixedArrayTable n ℚ)
    (hL : ∀ j, lengths.read j = (terminal (rounded true model W k values v hv) small).length j) :
    (GeneralPaperEqualMaterializedPacking.run (terminal (rounded true model W k values v hv) small) model A lengths hL
      (List.finRange n) (GeneralPaperEqualPreparationPrefix.uniform_items _ small).symm).2 ≤ packingBound model A n k := by
  apply GeneralPaperEqualMaterializedPacking.work
    (D := (GeneralPaperValueRoundingPaperContract.run true model W 256 k values).1.2)
  · exact (GeneralPaperValueRoundingPaperContract.positivity true model W 256 k (by decide) values v hv).1
  · norm_num [terminal]
  · have hOne : rationalWordWidth (1 : ℚ) = 3 := by decide
    change rationalWordWidth (1 : ℚ) ≤ _
    rw [hOne]
    omega
  · have h := denominator_word true model W k values v hv
    omega
  · intro j
    exact (lattice true model W k values v hv j).int_mul 2

theorem routes {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1)
    (p : RationalTerminalPacking (terminal (rounded true model W k values v hv) small))
    (lengths : FixedArrayTable n ℚ)
    (hL : ∀ j, lengths.read j = (terminal (rounded true model W k values v hv) small).length j) :
    (GeneralPaperEqualRouteConstruction.prepare p model A lengths hL).2 ≤ routeBound model A n k := by
  revert small
  rw [rounded_successor]
  intro small p hL
  simpa only [routeBound, Nat.add_assoc] using
    GeneralPaperEqualNativeRouteCost.native_work true model W A (k+1) values v hv small p lengths hL

theorem segments {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1)
    (p : RationalTerminalPacking (terminal (rounded true model W k values v hv) small)) :
    (GeneralPaperEqualNativeSegmentPreparation.prepared (rounded true model W k values v hv) small p model A).2 ≤
      segmentBound model A n k := by
  revert small
  rw [rounded_successor]
  intro small p
  exact (GeneralPaperEqualNativeSegmentPreparation.native_work true model W A (k+1) values v hv small p).trans_eq
    (by unfold segmentBound; congr 4)

end Blotto.GeneralPaperEqualFirstPrefixRates
