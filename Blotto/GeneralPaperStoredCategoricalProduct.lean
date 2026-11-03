import Blotto.GeneralPaperNaturalScalarStep

/-! The common denominator is produced once from stored probability words.
The actual array size drives the loop. Each multiplication, operand/result
word, reference and numeric loop-control step is charged. -/
namespace Blotto.GeneralPaperStoredCategoricalProduct
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1400000

def build {r : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A : ℕ) :
    (k : ℕ) → k ≤ r → ℕ × ℕ
  | 0, _ => (1, 64 * A + 64)
  | k + 1, hk =>
      let child := build weights model A k (by omega)
      let value := weights.read ⟨k, by omega⟩
      let denominator := value.den
      let product := GeneralPaperNaturalScalarStep.run model A .mul child.1 denominator
      (product.1, child.2 + rationalWordWidth value + product.2 +
        64 * (A + binaryWordWidth (k + 1) + 1))

theorem prefix_data {r : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A k : ℕ) (hk : k ≤ r) :
    (build weights model A k hk).1 = ∏ j : Fin k, (weights.read ⟨j.val, by omega⟩).den := by
  induction k with
  | zero => simp only [build, Finset.univ_eq_empty, Finset.prod_empty]
  | succ k ih =>
    rw [build]
    dsimp only [GeneralPaperNaturalScalarStep.run, GeneralPaperNaturalScalarStep.Op.apply]
    rw [ih (by omega), Fin.prod_univ_castSucc]
    rfl

def run {r : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A : ℕ) : ℕ × ℕ :=
  build weights model A weights.data.size weights.size.le

theorem transported_product {r : ℕ} (weights : FixedArrayTable r ℚ) (size : ℕ) (hSize : size = r) :
    (∏ j : Fin size, (weights.read (j.cast hSize)).den) = ∏ j : Fin r, (weights.read j).den := by
  cases hSize
  rfl

theorem data {r : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A : ℕ) :
    (run weights model A).1 = GeneralPaperEqualCategoricalIntegerData.denominator weights.read := by
  rw [run, prefix_data]
  exact transported_product weights weights.data.size weights.size

theorem prepared_data {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) :
    (run p.weights model A).1 = GeneralPaperEqualCategoricalIntegerData.denominator p.lottery.weight :=
  data p.weights model A

theorem value_bound {r s : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A k : ℕ) (hk : k ≤ r)
    (h : ∀ j, RationalHeight (weights.read j) s) : (build weights model A k hk).1 ≤ 2 ^ (s * k) := by
  induction k with
  | zero => simp only [build, Nat.mul_zero, pow_zero, le_rfl]
  | succ k ih =>
    have hc := ih (by omega)
    have hd := (h ⟨k, by omega⟩).2.le
    rw [build]
    dsimp only [GeneralPaperNaturalScalarStep.run, GeneralPaperNaturalScalarStep.Op.apply]
    calc
      _ ≤ 2 ^ (s * k) * 2 ^ s := Nat.mul_le_mul hc hd
      _ = _ := by rw [← pow_add]; congr 1

theorem power_word (a e : ℕ) (h : a ≤ 2 ^ e) : GeneralPaperNaturalScalarStep.word a ≤ e + 2 := by
  have hw := binaryWordWidth_mono h
  have hPow : binaryWordWidth (2 ^ e) = e + 1 := by simp only [binaryWordWidth, Nat.log2_two_pow]
  rw [hPow] at hw
  unfold GeneralPaperNaturalScalarStep.word
  omega

def stepBound (model : RationalCostModel) (A r s : ℕ) : ℕ :=
  1 + 2 * s + 5 * model.rat (s * r + 2) + 80 * (A + binaryWordWidth (r + 1) + 1)

theorem build_work {r s : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A k : ℕ) (hk : k ≤ r)
    (h : ∀ j, RationalHeight (weights.read j) s) :
    (build weights model A k hk).2 ≤ k * stepBound model A r s + 64 * A + 64 := by
  induction k with
  | zero => simp only [build, Nat.zero_mul, Nat.zero_add, le_rfl]
  | succ k ih =>
    have hc := ih (by omega)
    have hv := value_bound weights model A k (by omega) h
    have hd := (h ⟨k, by omega⟩).2.le
    have hExp : s * k + s ≤ s * r := by nlinarith only [hk]
    have hm : (build weights model A k (by omega)).1 * (weights.read ⟨k, by omega⟩).den ≤ 2 ^ (s * r) := by
      calc
        _ ≤ 2 ^ (s * k) * 2 ^ s := Nat.mul_le_mul hv hd
        _ ≤ _ := by rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) hExp
    have hPrev := hv.trans (Nat.pow_le_pow_right (by decide) (show s * k ≤ s * r by omega))
    have hDen := hd.trans (Nat.pow_le_pow_right (by decide) (show s ≤ s * r by nlinarith only [hk]))
    have hStep := GeneralPaperNaturalScalarStep.work model A .mul
      (build weights model A k (by omega)).1 (weights.read ⟨k, by omega⟩).den (s * r + 2)
      (power_word _ _ hPrev) (power_word _ _ hDen) (power_word _ _ hm)
    have hQ := rationalWordWidth_of_height (h ⟨k, by omega⟩)
    have hIndex := binaryWordWidth_mono (show k + 1 ≤ r + 1 by omega)
    rw [build]
    dsimp only
    unfold stepBound at hc ⊢
    nlinarith only [hc, hStep, hQ, hIndex]

theorem work {r s : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A : ℕ)
    (h : ∀ j, RationalHeight (weights.read j) s) :
    (run weights model A).2 ≤ r * stepBound model A r s + 64 * A + 64 := by
  have hw := build_work weights model A weights.data.size weights.size.le h
  exact hw.trans_eq (by rw [weights.size])

end Blotto.GeneralPaperStoredCategoricalProduct
