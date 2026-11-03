import Blotto.GeneralPaperGridScalarPayoffs

/-! Exhaustive symbolic coverage of all poor-player integer bids, not a
finite numerical experiment. The parameter q is any integer at least three. -/
namespace Blotto.GeneralPaperGridIntegerResponses
open GeneralPaperGridScalarPayoffs
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem poor_bound (q y : ℕ) (hq : 3 ≤ q) (hy : y ≤ 2*q) : poorMean (q : ℝ) (y : ℝ) ≤ 1/3 := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hyR : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  by_cases hLow : y + 2 ≤ q
  · have h : (y : ℝ) + 2 ≤ q := by exact_mod_cast hLow
    exact poor_low _ _ (by linarith) hyR (by linarith)
  · by_cases hA : y + 1 = q
    · have h : (y : ℝ) + 1 = q := by exact_mod_cast hA
      have he : (y : ℝ) = (q : ℝ) - 1 := by linarith
      rw [he]
      exact (poor_boundaries _ hqR).1.le
    · by_cases hB : y = q
      · subst y
        exact (poor_boundaries _ hqR).2.1.le
      · by_cases hC : y = 2*q
        · subst y
          push_cast
          exact (poor_boundaries _ hqR).2.2.le
        · have hLeft : q + 1 ≤ y := by omega
          have hRight : y + 1 ≤ 2*q := by omega
          have hL : (q : ℝ) + 1 ≤ y := by exact_mod_cast hLeft
          have hR : (y : ℝ) + 1 ≤ 2*(q : ℝ) := by exact_mod_cast hRight
          exact poor_middle _ _ (by linarith) hL (by linarith)

end Blotto.GeneralPaperGridIntegerResponses
