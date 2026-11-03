import Blotto.AdaptiveEntropyTrajectory

/-! Constructed proof-only auxiliary entropy iterates give the uniform signed
noise bound. The final comparator may depend on the whole random history.
The actual learner must still supply its rounded pathwise regret and native
transition/saddle-law contracts. -/

namespace Blotto
open scoped BigOperators Classical
namespace SparseMW

def simplexComparators (n : ℕ) : Set (Fin n → ℝ) :=
  {u | (∀ i, 0 ≤ u i) ∧ (∑ i, u i) = 1}

theorem expected_regret_with_constructed_auxiliary {a n : ℕ} (hn : 0 < n)
    (transition : List (Fin a) → Fin a → ℝ)
    (hp : ∀ past x, 0 ≤ transition past x) (hs : ∀ past, ∑ x, transition past x = 1)
    (empirical noise : List (Fin a) → Fin a → Fin n → ℝ)
    (hz : ∀ past i, ∑ x, transition past x * noise past x i = 0)
    (hnoise : ∀ past x i, |noise past x i| ≤ 1)
    (actual : List (Fin a) → Fin n → ℝ) (eta boundActual : ℝ) (heta : 0 ≤ eta) (T : ℕ)
    (hActual : ∀ past, past.length = T → ∀ u, u ∈ simplexComparators n →
      eta * cumulativePairing empirical actual u past ≤ boundActual)
    (selectedComparator : List (Fin a) → Fin n → ℝ)
    (hSelected : ∀ past, selectedComparator past ∈ simplexComparators n) :
    eta * historyMean transition T (fun past =>
      cumulativePairing (fun h x i => empirical h x i - noise h x i) actual (selectedComparator past) past) ≤
        boundActual + Real.log n + (eta ^ 2 / 2) * T := by
  let negativeNoise := fun h x i => -noise h x i
  let auxiliary := entropyHistory negativeNoise eta
  have haux : ∀ past, past.length = T → ∀ u, u ∈ simplexComparators n →
      eta * cumulativePairing negativeNoise auxiliary u past ≤ Real.log n + (eta ^ 2 / 2) * T := by
    intro past hlength u hu
    have he := entropyHistory_uniform_regret hn negativeNoise eta 1 heta
      (fun h x i => by simpa only [negativeNoise, abs_neg] using hnoise h x i) u hu.1 hu.2 past
    simpa only [hlength, one_pow, mul_one] using he
  have he := expected_uniform_true_regret_scaled transition hp hs empirical noise hz actual auxiliary
    (simplexComparators n) eta boundActual (Real.log n + (eta ^ 2 / 2) * T) T hActual haux selectedComparator hSelected
  convert he using 1
  ring

end SparseMW
end Blotto
