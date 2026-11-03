import Blotto.RoundingTree
import Blotto.ThreeMarginals

/-! Exact linear dependence of marginal measures on resource coefficients. -/

namespace Blotto
open MeasureTheory Set

noncomputable def affineMeasure (q : ℝ) (A D : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal q • A + ENNReal.ofReal (1 - q) • D

theorem binary_affineMeasure (p q r : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq : 0 ≤ q ∧ q ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1) (A D : Measure ℝ) :
    ENNReal.ofReal p • affineMeasure q A D + ENNReal.ofReal (1 - p) • affineMeasure r A D =
      affineMeasure (p * q + (1 - p) * r) A D := by
  have hp' := sub_nonneg.mpr hp.2
  have hq' := sub_nonneg.mpr hq.2
  have hr' := sub_nonneg.mpr hr.2
  have hAq := mul_nonneg hp.1 hq.1
  have hAr := mul_nonneg hp' hr.1
  have hDq := mul_nonneg hp.1 hq'
  have hDr := mul_nonneg hp' hr'
  have hcoef : p * (1 - q) + (1 - p) * (1 - r) = 1 - (p * q + (1 - p) * r) := by ring
  rw [affineMeasure, affineMeasure, affineMeasure, smul_add, smul_add,
    smul_smul, smul_smul, smul_smul, smul_smul,
    ← ENNReal.ofReal_mul hp.1, ← ENNReal.ofReal_mul hp.1,
    ← ENNReal.ofReal_mul hp', ← ENNReal.ofReal_mul hp']
  calc
    _ = ENNReal.ofReal (p * q + (1 - p) * r) • A +
        ENNReal.ofReal (p * (1 - q) + (1 - p) * (1 - r)) • D := by
      rw [ofReal_smul_add hAq hAr, ofReal_smul_add hDq hDr]
      simp only [add_assoc, add_left_comm]
    _ = _ := by rw [hcoef]

namespace RoundingTree

/-- Leaf resource coefficients average to the tree's initial coefficient as
actual marginal measures, rather than only as a numerical expectation. -/
theorem eval_affine_marginal {n m : ℕ} (T : RoundingTree n) (leafLaw : Allocation n → Mixed m)
    (capacity : Allocation n) (hcap : ∀ i, 0 < capacity i) (index : Fin n) (j : Fin m)
    (A D : Measure ℝ) (hbox : T.ForLeaves (InBox capacity))
    (hm : T.ForLeaves (fun r => (marginal (leafLaw r) j : Measure ℝ) =
      affineMeasure (r index / capacity index) A D)) :
    (marginal (T.eval leafLaw) j : Measure ℝ) =
      affineMeasure (T.average index / capacity index) A D := by
  induction T with
  | leaf r => exact hm
  | fork p hp a b ha hb =>
    have hA := a.average_inBox capacity hbox.1
    have hB := b.average_inBox capacity hbox.2
    have hq : 0 ≤ a.average index / capacity index ∧ a.average index / capacity index ≤ 1 :=
      ⟨div_nonneg (hA index).1 (le_of_lt (hcap index)), (div_le_one (hcap index)).mpr (hA index).2⟩
    have hr : 0 ≤ b.average index / capacity index ∧ b.average index / capacity index ≤ 1 :=
      ⟨div_nonneg (hB index).1 (le_of_lt (hcap index)), (div_le_one (hcap index)).mpr (hB index).2⟩
    rw [eval, binaryLaw_marginal, ha hbox.1 hm.1, hb hbox.2 hm.2,
      binary_affineMeasure p _ _ hp hq hr]
    congr 1
    dsimp [average]
    ring

end RoundingTree
end Blotto
