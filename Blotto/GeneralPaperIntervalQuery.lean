import Blotto.GeneralPaperPrefixInterval

/-! Separately round an exact interval numerator, with the common whole-
block denominator. Runtime uses prebuilt low/high ranks. It never subtracts
two rounded CDF counts and never normalizes a sign independently.
-/
namespace Blotto.GeneralPaperIntervalQuery
open scoped BigOperators
open GeneralPaperPrefixInterval
set_option autoImplicit false
set_option maxHeartbeats 3500000

def evaluate {n : ℕ} (k : ℕ) (preparedPrefix : FixedArrayTable (n+1) ℕ) (lo hi : Fin (n+1)) :
    GeneralPaperBoundedQuotient.Result :=
  let result := GeneralPaperCDFMesh.selected k (numerator preparedPrefix lo hi) (preparedPrefix.read (Fin.last n))
  ⟨result.quotient,result.remainder,result.work+24⟩

def cached {n m : ℕ} (k : ℕ) (preparedPrefix : FixedArrayTable (n+1) ℕ)
    (ranks : FixedArrayTable m (Fin (n+1))) (lo hi : Fin m) : GeneralPaperBoundedQuotient.Result :=
  let result := evaluate k preparedPrefix (ranks.read lo) (ranks.read hi)
  ⟨result.quotient,result.remainder,result.work+16⟩

theorem count_bound {n : ℕ} (k : ℕ) (values : FixedArrayTable n ℕ) (lo hi : Fin (n+1))
    (hTotal : 0<∑ r, values.read r) :
    (evaluate k (GeneralPaperEpochPrefixArray.build values) lo hi).quotient≤(GeneralPaperSourceParameters.prepare k).meshDenominator :=
  (GeneralPaperCDFMesh.selected_bounds k _ _
    (by rw [GeneralPaperEpochPrefixQuery.read_total]; exact hTotal) (numerator_le_total values lo hi)).1

theorem value_bounds {n : ℕ} (k : ℕ) (values : FixedArrayTable n ℕ) (lo hi : Fin (n+1))
    (hTotal : 0<∑ r, values.read r) :
    0≤GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator
      (evaluate k (GeneralPaperEpochPrefixArray.build values) lo hi).quotient ∧
    GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator
      (evaluate k (GeneralPaperEpochPrefixArray.build values) lo hi).quotient≤1 :=
  GeneralPaperRoundedLosses.component_bounds _ _ (GeneralPaperSourceParameters.mesh_positive k) (count_bound k values lo hi hTotal)

theorem rounding_error {n : ℕ} (k : ℕ) (values : FixedArrayTable n ℕ) (lo hi : Fin (n+1))
    (hTotal : 0<∑ r, values.read r) :
    |(numerator (GeneralPaperEpochPrefixArray.build values) lo hi:ℝ)/
        ((GeneralPaperEpochPrefixArray.build values).read (Fin.last n):ℝ)-
      (GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator
        (evaluate k (GeneralPaperEpochPrefixArray.build values) lo hi).quotient:ℝ)|≤
      ((GeneralPaperSourceParameters.prepare k).theta:ℝ) :=
  GeneralPaperCDFMesh.selected_real_error k _ _
    (by rw [GeneralPaperEpochPrefixQuery.read_total]; exact hTotal) (numerator_le_total values lo hi)

theorem lower_count_antitone {n : ℕ} (k : ℕ) (values : FixedArrayTable n ℕ) (hi : Fin (n+1))
    (hTotal : 0<∑ r, values.read r) :
    Antitone (fun lo => (evaluate k (GeneralPaperEpochPrefixArray.build values) lo hi).quotient) := by
  intro small large hOrder
  exact GeneralPaperCDFMesh.evaluate_monotone _ _ _ _ _
    (by rw [GeneralPaperEpochPrefixQuery.read_total]; exact hTotal)
    (numerator_le_total values small hi) (lower_antitone values hi hOrder) (GeneralPaperCDFMesh.selected_depth k)

theorem empty_count {n : ℕ} (k : ℕ) (values : FixedArrayTable n ℕ) (rank : Fin (n+1))
    (hTotal : 0<∑ r, values.read r) : (evaluate k (GeneralPaperEpochPrefixArray.build values) rank rank).quotient=0 := by
  unfold evaluate
  rw [GeneralPaperPrefixInterval.empty]
  exact GeneralPaperCDFMesh.evaluate_zero _ _ _
    (by rw [GeneralPaperEpochPrefixQuery.read_total]; exact hTotal) (GeneralPaperCDFMesh.selected_depth k)

theorem evaluate_work {n : ℕ} (k : ℕ) (preparedPrefix : FixedArrayTable (n+1) ℕ) (lo hi : Fin (n+1)) :
    (evaluate k preparedPrefix lo hi).work=12*(30+k)+42 := by
  unfold evaluate
  dsimp only
  rw [GeneralPaperCDFMesh.selected_work]

theorem cached_work {n m : ℕ} (k : ℕ) (preparedPrefix : FixedArrayTable (n+1) ℕ)
    (ranks : FixedArrayTable m (Fin (n+1))) (lo hi : Fin m) :
    (cached k preparedPrefix ranks lo hi).work=12*(30+k)+58 := by
  unfold cached
  dsimp only
  rw [evaluate_work]

end Blotto.GeneralPaperIntervalQuery
