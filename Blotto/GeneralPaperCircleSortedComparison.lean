import Blotto.GeneralPaperCircleNativePayoff

/-! A concrete mathematical sorting permutation removes the supplied
sorted-row premise. Budgets and comparison payoffs use every original
representative exactly once. Deviations are not sorted against the row.
Native row-sort/sweep execution and its prices remain separate obligations. -/
namespace Blotto.GeneralPaperCircleSortedComparison
open GeneralPaperCircleFiniteAverage GeneralPaperCircleLightPayoff
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable def sorted {R : ℕ} (x : Fin R → ℝ) : Fin R → ℝ := fun a => x (Tuple.sort x a)

theorem sorted_monotone {R : ℕ} (x : Fin R → ℝ) : Monotone (sorted x) := Tuple.monotone_sort x

theorem sorted_sum {R : ℕ} (x : Fin R → ℝ) : (∑ a,sorted x a)=∑ a,x a := Equiv.sum_comp (Tuple.sort x) x

theorem sorted_feasible {h R : ℕ} (kept : Allocation h) (x : Fin R → ℝ) (B : ℝ)
    (hRow : Feasible B (Fin.addCases kept x)) : Feasible B (Fin.addCases kept (sorted x)) := by
  constructor
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simpa only [Fin.addCases_left] using hRow.1 (Fin.castAdd R i)
    · intro a
      simpa only [Fin.addCases_right,sorted] using hRow.1 (Fin.natAdd h (Tuple.sort x a))
  · rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left,Fin.addCases_right,sorted_sum]
    have hh := hRow.2
    rw [Fin.sum_univ_add] at hh
    simpa only [Fin.addCases_left,Fin.addCases_right] using hh

theorem comparison_sorted {g R : ℕ} (W : ℕ) (weights : Fin g → ℕ) (values y : Fin g → ℝ) (x : Fin R → ℝ) :
    comparison R W weights values y (sorted x)=comparison R W weights values y x := by
  unfold comparison
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact average_permutation (fun a => share (y j) (GeneralPaperCircleCoordinatePayoff.coefficient R W (weights j)*x a)) (Tuple.sort x)

theorem reconstruct_feasible {h g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (hs : ∑ j,weights j=W) (kept : Allocation h) (x : Fin R → ℝ) (B : ℝ)
    (hRow : Feasible B (Fin.addCases kept x)) (shift : ℕ) :
    Feasible B (GeneralPaperCircleHardBudget.reconstruct R W hR hW weights kept (sorted x) shift) :=
  GeneralPaperCircleHardBudget.reconstruct_feasible R W hR hW weights hs kept (sorted x) (sorted_monotone x) B
    (sorted_feasible kept x B hRow) shift

theorem error_sorted {g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (values : Fin g → ℝ) (hv : ∀ j,0≤values j) (y : Fin g → ℝ) (x : Fin R → ℝ) :
    0≤reconstructed R W hR hW weights values y (sorted x)-comparison R W weights values y x ∧
      reconstructed R W hR hW weights values y (sorted x)-comparison R W weights values y x≤loss W weights values := by
  simpa only [comparison_sorted] using error R W hR hW weights values hv y (sorted x) (sorted_monotone x)

theorem mixture_error_sorted {T g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (values : Fin g → ℝ) (hv : ∀ j,0≤values j) (y : Fin g → ℝ) (rows : Fin T → Fin R → ℝ)
    (p : Fin T → ℝ) (hp : ∀ r,0≤p r) (hs : ∑ r,p r=1) :
    0≤(∑ r,p r*reconstructed R W hR hW weights values y (sorted (rows r)))-
        (∑ r,p r*comparison R W weights values y (rows r)) ∧
      (∑ r,p r*reconstructed R W hR hW weights values y (sorted (rows r)))-
        (∑ r,p r*comparison R W weights values y (rows r))≤loss W weights values := by
  simpa only [comparison_sorted] using mixture_error R W hR hW weights values hv y
    (fun r => sorted (rows r)) (fun r => sorted_monotone (rows r)) p hp hs

theorem native_error_sorted {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (hg : 0<(GeneralPaperOriginalValueReduction.run bits model W k values).1.classified.light.size)
    (y : Fin (GeneralPaperOriginalValueReduction.run bits model W k values).1.classified.light.size → ℝ)
    (x : Fin (GeneralPaperLightFieldReduction.representatives k) → ℝ) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k values).1
    let hR := GeneralPaperLightFieldReduction.representatives_positive k
    let hL := GeneralPaperCircleActualWeights.original_total_positive bits model W k values v hv hg
    0≤reconstructed _ _ hR hL (GeneralPaperCircleActualWeights.weights o)
        (GeneralPaperCircleNativePayoff.lightValues o) y (sorted x)-
      comparison (GeneralPaperLightFieldReduction.representatives k) o.classified.lightWeight
        (GeneralPaperCircleActualWeights.weights o) (GeneralPaperCircleNativePayoff.lightValues o) y x ∧
      reconstructed _ _ hR hL (GeneralPaperCircleActualWeights.weights o)
        (GeneralPaperCircleNativePayoff.lightValues o) y (sorted x)-
      comparison (GeneralPaperLightFieldReduction.representatives k) o.classified.lightWeight
        (GeneralPaperCircleActualWeights.weights o) (GeneralPaperCircleNativePayoff.lightValues o) y x≤(1/(2:ℝ)^k)/10 := by
  simpa only [comparison_sorted] using GeneralPaperCircleNativePayoff.original_error bits model W k values v hv hg y
    (sorted x) (sorted_monotone x)

end Blotto.GeneralPaperCircleSortedComparison
