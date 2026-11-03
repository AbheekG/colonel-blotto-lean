import Blotto.GeneralPaperSizedBitArray

/-! Selected cached segment interpolation and original-budget scaling. The
midpoint is supplied once, each group coordinate is computed once, and the
resulting small array is materialized with indexed/control prices included. -/
namespace Blotto.GeneralPaperEqualBitGroups
open scoped BigOperators
open GeneralPaperEqualPreparedCache (Prepared)
open GeneralPaperPositiveSegmentCompaction (count compact)
open GeneralPaperRationalScalarStep
set_option autoImplicit false
set_option maxHeartbeats 900000

def coordinate (model : RationalCostModel) (A : ℕ) (B t P Q : ℚ) : ℚ × ℕ :=
  let complement := GeneralPaperRationalScalarStep.run model A .sub 1 t
  let first := GeneralPaperRationalScalarStep.run model A .mul complement.1 P
  let second := GeneralPaperRationalScalarStep.run model A .mul t Q
  let total := GeneralPaperRationalScalarStep.run model A .add first.1 second.1
  let scaled := GeneralPaperRationalScalarStep.run model A .mul B total.1
  (scaled.1, complement.2 + first.2 + second.2 + total.2 + scaled.2)

theorem coordinate_data (model : RationalCostModel) (A : ℕ) (B t P Q : ℚ) :
    (coordinate model A B t P Q).1 = B * ((1 - t) * P + t * Q) := rfl

theorem coordinate_work (model : RationalCostModel) (A : ℕ) (B t P Q : ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hB : RationalHeight B s) (ht : RationalHeight t s) (hP : RationalHeight P s) (hQ : RationalHeight Q s) :
    (coordinate model A B t P Q).2 ≤ 25 * model.rat (1 + 2 * expressionHeightBudget s 3) + 80 * A + 80 := by
  let H := expressionHeightBudget s 3
  have hS : 6 * s + 2 ≤ H := by dsimp [H, expressionHeightBudget]; omega
  have hm : s ≤ H := expressionHeightBudget_ge_input s 3
  have hOne : RationalHeight (1 : ℚ) s := (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hC := hOne.sub ht
  have hFirst := hC.mul hP
  have hSecond := ht.mul hQ
  have hTotal := hFirst.add hSecond
  have hScaled := hB.mul hTotal
  have hC' := hC.mono (show s + s + 1 ≤ H by omega)
  have hFirst' := hFirst.mono (show s + s + 1 + s ≤ H by omega)
  have hSecond' := hSecond.mono (show s + s ≤ H by omega)
  have hTotal' := hTotal.mono (show s + s + 1 + s + (s + s) + 1 ≤ H by omega)
  have hScaled' := hScaled.mono (show s + (s + s + 1 + s + (s + s) + 1) ≤ H by
    dsimp [H, expressionHeightBudget]; omega)
  have h1 := GeneralPaperRationalScalarStep.work model A .sub 1 t H (hOne.mono hm) (ht.mono hm) hC'
  have h2 := GeneralPaperRationalScalarStep.work model A .mul (1 - t) P H hC' (hP.mono hm) hFirst'
  have h3 := GeneralPaperRationalScalarStep.work model A .mul t Q H (ht.mono hm) (hQ.mono hm) hSecond'
  have h4 := GeneralPaperRationalScalarStep.work model A .add ((1 - t) * P) (t * Q) H hFirst' hSecond' hTotal'
  have h5 := GeneralPaperRationalScalarStep.work model A .mul B ((1 - t) * P + t * Q) H (hB.mono hm) hTotal' hScaled'
  unfold coordinate
  dsimp only [GeneralPaperRationalScalarStep.run, Op.apply] at h1 h2 h3 h4 h5 ⊢
  change _ ≤ 25 * model.rat (1 + 2 * H) + 80 * A + 80
  omega

def run {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ) (slot : Fin (count l)) (t : ℚ) : FixedArrayTable m ℚ × ℕ :=
  let P := p.segments.left.read slot
  let Q := p.segments.right.read slot
  let returned := GeneralPaperSizedBitArray.run P.data.size P.size A
    (fun g => coordinate model A p.budget t (P.read g) (Q.read g))
  (returned.1, returned.2 + 32 * A + 32)

theorem data {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ) (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool) :
    (run p model A slot (GeneralPaperEqualPreparedCache.midpoint p fresh)).1 =
      GeneralPaperEqualCachedEmission.scaledPoint p slot fresh := by
  unfold run
  dsimp only
  rw [GeneralPaperSizedBitArray.eq_run, PaperIndexedArrayConstruction.run_data]
  congr 1
  funext g
  simp only [coordinate_data, GeneralPaperEqualPreparedCache.groupPoint,
    FixedArrayTable.read_ofFn]

def base (s b K : ℕ) : ℕ := max b (max s (K + 2))
def height (s b K : ℕ) : ℕ := expressionHeightBudget (base s b K) 3

theorem work {n m k s b : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ) (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool)
    (hs : 2 ≤ s) (h : l.HeightAt s) (hB : RationalHeight p.budget b) :
    (run p model A slot (GeneralPaperEqualPreparedCache.midpoint p fresh)).2 ≤
      25 * m * model.rat (1 + 2 * height s b p.midpointBits) +
      128 * (m + 1) * (A + 1) + PaperIndexedArrayConstruction.overhead (fun w => w) A m m := by
  let H := base s b p.midpointBits
  have hS : s ≤ H := (le_max_left s (p.midpointBits + 2)).trans (le_max_right _ _)
  have hT : p.midpointBits + 2 ≤ H := (le_max_right s (p.midpointBits + 2)).trans (le_max_right _ _)
  have hB' : RationalHeight p.budget H := hB.mono (le_max_left _ _)
  have ht : RationalHeight (GeneralPaperEqualPreparedCache.midpoint p fresh) H := by
    rw [GeneralPaperEqualPreparedCache.midpoint_eq]
    exact (dyadicMidpointSample_height _ _).mono hT
  have hComp := GeneralPaperPositiveSegmentCompaction.compact_height l h
  have hP : ∀ g, RationalHeight ((p.segments.left.read slot).read g) H := by
    intro g
    rw [p.segments.left_correct]
    exact (hComp.2 slot g).1.mono hS
  have hQ : ∀ g, RationalHeight ((p.segments.right.read slot).read g) H := by
    intro g
    rw [p.segments.right_correct]
    exact (hComp.2 slot g).2.mono hS
  have hc : (∑ g, (coordinate model A p.budget (GeneralPaperEqualPreparedCache.midpoint p fresh)
      ((p.segments.left.read slot).read g) ((p.segments.right.read slot).read g)).2) ≤
      m * (25 * model.rat (1 + 2 * expressionHeightBudget H 3) + 80 * A + 80) := by
    calc
      _ ≤ ∑ _g : Fin m, (25 * model.rat (1 + 2 * expressionHeightBudget H 3) + 80 * A + 80) :=
        Finset.sum_le_sum (fun g _ => coordinate_work model A _ _ _ _ H (hs.trans hS) hB' ht (hP g) (hQ g))
      _ = _ := by simp
  unfold run
  dsimp only
  rw [GeneralPaperSizedBitArray.eq_run, PaperIndexedArrayConstruction.run_work]
  change _ ≤ 25 * m * model.rat (1 + 2 * expressionHeightBudget H 3) + 128 * (m + 1) * (A + 1) + _
  nlinarith only [hc]

end Blotto.GeneralPaperEqualBitGroups
