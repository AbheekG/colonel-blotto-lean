import Blotto.Model
import Mathlib.Analysis.LocallyConvex.Separation

/-! A derived nonnegative normalized separating vector for a compact convex
finite payoff image disjoint from a lower orthant. The linear functional and
its weights are constructed by separation, not supplied as a minimax oracle. -/

namespace Blotto.FinitePayoffSeparation
open Set
open scoped BigOperators Classical

def lowerOrthant {k : ℕ} (threshold : ℝ) : Set (Fin k → ℝ) :=
  {row | ∀ j, row j ≤ threshold}

theorem lowerOrthant_convex {k : ℕ} (threshold : ℝ) :
    Convex ℝ (lowerOrthant (k := k) threshold) := by
  intro x hx y hy a b ha hb hSum j
  change a * x j + b * y j ≤ threshold
  have hx' := mul_le_mul_of_nonneg_left (hx j) ha
  have hy' := mul_le_mul_of_nonneg_left (hy j) hb
  calc
    _ ≤ a * threshold + b * threshold := add_le_add hx' hy'
    _ = (a + b) * threshold := by ring
    _ = threshold := by rw [hSum,one_mul]

theorem lowerOrthant_closed {k : ℕ} (threshold : ℝ) :
    IsClosed (lowerOrthant (k := k) threshold) := by
  have he : lowerOrthant (k := k) threshold = ⋂ j : Fin k, {row | row j ≤ threshold} := by
    ext row; simp [lowerOrthant]
  rw [he]
  exact isClosed_iInter fun j => isClosed_le (continuous_apply j) continuous_const

theorem dual_sum {k : ℕ} (f : StrongDual ℝ (Fin k → ℝ)) (row : Fin k → ℝ) :
    f row = ∑ j, row j * f (Pi.single j 1) := by
  have he : row = ∑ j, row j • Pi.single j (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc
    f row = f (∑ j, row j • Pi.single j (1 : ℝ)) := congrArg f he
    _ = _ := by rw [map_sum]; simp only [map_smul,smul_eq_mul]

theorem coefficients_nonnegative {k : ℕ} (f : StrongDual ℝ (Fin k → ℝ))
    (threshold bound : ℝ) (hBound : ∀ row ∈ lowerOrthant threshold, f row < bound) :
    ∀ j, 0 ≤ f (Pi.single j 1) := by
  intro j
  by_contra hFail
  have hNegative : f (Pi.single j 1) < 0 := lt_of_not_ge hFail
  let base : Fin k → ℝ := fun _ => threshold
  let amount : ℝ := (|bound| + |f base| + 1) / (-f (Pi.single j 1))
  have hAmount : 0 ≤ amount := div_nonneg (by positivity) (neg_pos.mpr hNegative).le
  let row : Fin k → ℝ := base - amount • Pi.single j 1
  have hRow : row ∈ lowerOrthant threshold := by
    intro i
    change threshold - amount * ((Pi.single j (1 : ℝ) : Fin k → ℝ) i) ≤ threshold
    by_cases hi : i = j
    · subst i; simpa using hAmount
    · simp [hi]
  have hValue : f row = f base - amount * f (Pi.single j 1) := by
    dsimp [row]
    rw [map_sub, map_smul, smul_eq_mul]
  have hProduct : amount * (-f (Pi.single j 1)) = |bound| + |f base| + 1 :=
    div_mul_cancel₀ _ (ne_of_gt (neg_pos.mpr hNegative))
  have hContradiction := hBound row hRow
  rw [hValue] at hContradiction
  nlinarith [le_abs_self bound, neg_abs_le (f base)]

/-- Strict separation of a nonempty compact convex image produces an
actual probability vector that secures more than the lower-orthant threshold
on every image point. No finite game minimax theorem is assumed. -/
theorem exists_probability_separator {k : ℕ} (image : Set (Fin k → ℝ))
    (hNonempty : image.Nonempty) (hConvex : Convex ℝ image) (hCompact : IsCompact image)
    (threshold : ℝ) (hDisjoint : Disjoint (lowerOrthant threshold) image) :
    ∃ weight : Fin k → ℝ, (∀ j, 0 ≤ weight j) ∧ (∑ j, weight j) = 1 ∧
      ∀ row ∈ image, threshold < ∑ j, weight j * row j := by
  obtain ⟨f,u,v,hLower,hGap,hImage⟩ := geometric_hahn_banach_closed_compact
    (lowerOrthant_convex threshold) (lowerOrthant_closed threshold) hConvex hCompact hDisjoint
  have hCoefficient := coefficients_nonnegative f threshold u hLower
  let total : ℝ := ∑ j, f (Pi.single j 1)
  have hTotal : 0 < total := by
    have hNonnegative : 0 ≤ total := Finset.sum_nonneg fun j _ => hCoefficient j
    by_contra hFail
    have hZero : total = 0 := le_antisymm (le_of_not_gt hFail) hNonnegative
    have hEach : ∀ j, f (Pi.single j 1) = 0 := by
      intro j
      have hLe := Finset.single_le_sum (fun i _ => hCoefficient i) (Finset.mem_univ j)
      change f (Pi.single j 1) ≤ total at hLe
      exact le_antisymm (hLe.trans_eq hZero) (hCoefficient j)
    have hFunctional : ∀ row, f row = 0 := by intro row; rw [dual_sum]; simp [hEach]
    obtain ⟨row,hRow⟩ := hNonempty
    have hFirst := hLower (fun _ => threshold) (fun _ => le_rfl)
    have hLast := hImage row hRow
    rw [hFunctional] at hFirst hLast
    linarith
  let weight : Fin k → ℝ := fun j => f (Pi.single j 1) / total
  refine ⟨weight,(fun j => div_nonneg (hCoefficient j) hTotal.le),?_,?_⟩
  · change (∑ j, f (Pi.single j 1) / total) = 1
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    exact mul_inv_cancel₀ hTotal.ne'
  · intro row hRow
    have hLowerConstant := hLower (fun _ => threshold) (fun _ => le_rfl)
    have hHigher := hImage row hRow
    have hConstant : f (fun _ => threshold) = threshold * total := by
      rw [dual_sum, ← Finset.mul_sum]
    have hWeighted : (∑ j, weight j * row j) = f row / total := by
      rw [dual_sum]
      simp only [weight, div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hWeighted]
    apply (lt_div_iff₀ hTotal).mpr
    rw [hConstant] at hLowerConstant
    linarith

end Blotto.FinitePayoffSeparation
