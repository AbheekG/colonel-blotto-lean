import Blotto.RationalOverlapGluing

/-! Native finite overlap descriptors. Empty/degenerate pairs get zero
weight and a fixed feasible budget row, exactly as in the real descriptor. -/

namespace Blotto.RationalOverlapGluing
open MeasureTheory
open scoped BigOperators

def safeP {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) : Fin 4 → ℚ :=
  if 0 < G.weight i j then G.curve i j (G.lower i j) else ![B, 0, 0, 0]

def safeQ {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) : Fin 4 → ℚ :=
  if 0 < G.weight i j then G.curve i j (G.upper i j) else ![B, 0, 0, 0]

theorem safeP_real {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) :
    (fun r => (G.safeP B i j r : ℝ)) = G.real.safeP B i j := by
  have he : 0 < G.weight i j ↔ 0 < G.real.weight i j := by rw [← G.weight_real]; norm_cast
  unfold safeP OverlapGluing.safeP
  by_cases hw : 0 < G.weight i j
  · rw [ite_eq_left hw, ite_eq_left (he.mp hw), G.curve_real, G.lower_real]
  · rw [ite_eq_right hw, ite_eq_right (fun h => hw (he.mpr h))]
    funext r
    fin_cases r <;> simp [budgetRow]

theorem safeQ_real {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) :
    (fun r => (G.safeQ B i j r : ℝ)) = G.real.safeQ B i j := by
  have he : 0 < G.weight i j ↔ 0 < G.real.weight i j := by rw [← G.weight_real]; norm_cast
  unfold safeQ OverlapGluing.safeQ
  by_cases hw : 0 < G.weight i j
  · rw [ite_eq_left hw, ite_eq_left (he.mp hw), G.curve_real, G.upper_real]
  · rw [ite_eq_right hw, ite_eq_right (fun h => hw (he.mpr h))]
    funext r
    fin_cases r <;> simp [budgetRow]

theorem weights_mass {k h : ℕ} (G : RationalOverlapGluing k h) : (∑ i, ∑ j, G.weight i j) = 1 := by
  have hm : (∑ i, ∑ j, (G.weight i j : ℝ)) = 1 := by
    simp_rw [G.weight_real]
    exact G.real.weights_mass
  exact_mod_cast hm

def descriptor {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) : RationalSegmentLottery 4 (k * h) where
  weight := fun r => G.weight (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2
  P := fun r => G.safeP B (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2
  Q := fun r => G.safeQ B (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2
  nonnegative := fun r => G.weight_nonnegative _ _
  mass := by
    have he := Equiv.sum_comp (finProdFinEquiv.symm : Fin (k * h) ≃ Fin k × Fin h) (fun r => G.weight r.1 r.2)
    rw [he]
    simpa only [← Finset.univ_product_univ, Finset.sum_product] using G.weights_mass

theorem descriptor_real {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) :
    (G.descriptor B).real = G.real.descriptor B := by
  apply SegmentLottery.eq_of_fields
  · funext r
    exact G.weight_real _ _
  · funext r
    exact G.safeP_real B _ _
  · funext r
    exact G.safeQ_real B _ _

end Blotto.RationalOverlapGluing
