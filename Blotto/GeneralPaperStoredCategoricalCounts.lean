import Blotto.GeneralPaperStoredCategoricalProduct

/-! Integer categorical data from the actual compact probability array.
The common denominator executes once. Count construction uses stored size,
and each quotient/product is evaluated once with explicit native bit prices. -/
namespace Blotto.GeneralPaperStoredCategoricalCounts
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1400000

def coordinate {r : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A D : ℕ) (i : Fin r) : ℕ × ℕ :=
  let q := weights.read i
  let quotient := GeneralPaperNaturalScalarStep.run model A .div D q.den
  let result := GeneralPaperNaturalScalarStep.run model A .mul q.num.toNat quotient.1
  (result.1, rationalWordWidth q + quotient.2 + result.2 + 64 * (A + binaryWordWidth (i.val + 1) + 1))

theorem coordinate_data {r : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A D : ℕ)
    (hD : D = GeneralPaperEqualCategoricalIntegerData.denominator weights.read) (i : Fin r) :
    (coordinate weights model A D i).1 = GeneralPaperEqualCategoricalIntegerData.count weights.read i := by
  unfold coordinate
  dsimp only [GeneralPaperNaturalScalarStep.run, GeneralPaperNaturalScalarStep.Op.apply]
  rw [hD]
  rfl

structure Data {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l) where
  D : ℕ
  D_correct : D = GeneralPaperEqualCategoricalIntegerData.denominator p.lottery.weight
  counts : FixedArrayTable r ℕ
  counts_correct : ∀ i, counts.read i = GeneralPaperEqualCategoricalIntegerData.count p.lottery.weight i

def run {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) : Data p × (ℕ × ℕ) :=
  let product := GeneralPaperStoredCategoricalProduct.run p.weights model A
  let counts := GeneralPaperSizedBitArray.run p.weights.data.size p.weights.size A (coordinate p.weights model A product.1)
  let actual : Data p := ⟨product.1, GeneralPaperStoredCategoricalProduct.prepared_data p model A,
    counts.1, (by
      intro i
      dsimp only [counts]
      rw [GeneralPaperSizedBitArray.eq_run, PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn]
      exact coordinate_data p.weights model A product.1 (GeneralPaperStoredCategoricalProduct.data p.weights model A) i)⟩
  (actual, (product.2, counts.2 + 64 * A + 64))

theorem numeric_bounds {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (D : ℕ) (hD : D = GeneralPaperEqualCategoricalIntegerData.denominator p.lottery.weight) (i : Fin r) :
    (p.weights.read i).den ≤ D ∧ (p.weights.read i).num.toNat ≤ D ∧
      D / (p.weights.read i).den ≤ D ∧ (p.weights.read i).num.toNat * (D / (p.weights.read i).den) ≤ D := by
  subst D
  have hPos := GeneralPaperEqualCategoricalIntegerData.denominator_pos p.lottery.weight
  have hDen := Nat.le_of_dvd hPos (GeneralPaperEqualCategoricalIntegerData.denominator_multiple p.lottery.weight i)
  have hQuot := Nat.div_pos hDen (p.weights.read i).den_pos
  change 0 < GeneralPaperEqualCategoricalIntegerData.denominator p.lottery.weight / (p.weights.read i).den at hQuot
  have hOut := GeneralPaperEqualCategoricalIntegerData.count_le_denominator p.lottery.weight p.lottery.nonnegative p.lottery.mass i
  change (p.weights.read i).num.toNat *
    (GeneralPaperEqualCategoricalIntegerData.denominator p.lottery.weight / (p.weights.read i).den) ≤ _ at hOut
  have hNum := Nat.mul_le_mul_left (p.weights.read i).num.toNat (show 1 ≤
    GeneralPaperEqualCategoricalIntegerData.denominator p.lottery.weight / (p.weights.read i).den by omega)
  simp only [Nat.mul_one] at hNum
  exact ⟨hDen, hNum.trans hOut, Nat.div_le_self _ _, hOut⟩

def stepBound (model : RationalCostModel) (A r s : ℕ) : ℕ :=
  1 + 2 * s + 10 * model.rat (s * r + 2) + 96 * (A + binaryWordWidth (r + 1) + 1)

theorem coordinate_work {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A D : ℕ)
    (hD : D = GeneralPaperEqualCategoricalIntegerData.denominator p.lottery.weight)
    (h : ∀ i, RationalHeight (p.weights.read i) s) (i : Fin r) :
    (coordinate p.weights model A D i).2 ≤ stepBound model A r s := by
  have hBounds := numeric_bounds p D hD i
  have hDW := GeneralPaperEqualCategoricalIntegerData.denominator_word p.lottery.weight h
  rw [← hD] at hDW
  have hWord : ∀ a ≤ D, GeneralPaperNaturalScalarStep.word a ≤ s * r + 2 := by
    intro a ha
    have hw := (binaryWordWidth_mono ha).trans hDW
    unfold GeneralPaperNaturalScalarStep.word
    omega
  have hDiv := GeneralPaperNaturalScalarStep.work model A .div D (p.weights.read i).den (s * r + 2)
    (hWord D le_rfl) (hWord _ hBounds.1) (hWord _ hBounds.2.2.1)
  have hMul := GeneralPaperNaturalScalarStep.work model A .mul (p.weights.read i).num.toNat
    (D / (p.weights.read i).den) (s * r + 2) (hWord _ hBounds.2.1) (hWord _ hBounds.2.2.1) (hWord _ hBounds.2.2.2)
  have hQ := rationalWordWidth_of_height (h i)
  have hIndex := binaryWordWidth_mono (show i.val + 1 ≤ r + 1 by omega)
  unfold coordinate stepBound
  dsimp only [GeneralPaperNaturalScalarStep.run, GeneralPaperNaturalScalarStep.Op.apply] at hDiv hMul ⊢
  omega

theorem work {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) (h : ∀ i, RationalHeight (p.weights.read i) s) :
    (run p model A).2.1 ≤ r * GeneralPaperStoredCategoricalProduct.stepBound model A r s + 64 * A + 64 ∧
      (run p model A).2.2 ≤ r * stepBound model A r s +
        PaperIndexedArrayConstruction.overhead id A r r + 64 * A + 64 := by
  have hP := GeneralPaperStoredCategoricalProduct.work p.weights model A h
  have hC := GeneralPaperPreparedSegmentCompaction.array_work p.weights.data.size p.weights.size A (stepBound model A r s)
    (coordinate p.weights model A (GeneralPaperStoredCategoricalProduct.run p.weights model A).1)
    (coordinate_work p model A _ (GeneralPaperStoredCategoricalProduct.prepared_data p model A) h)
  constructor
  · exact hP
  · change (GeneralPaperSizedBitArray.run p.weights.data.size p.weights.size A
      (coordinate p.weights model A (GeneralPaperStoredCategoricalProduct.run p.weights model A).1)).2 + 64 * A + 64 ≤ _
    omega

end Blotto.GeneralPaperStoredCategoricalCounts
