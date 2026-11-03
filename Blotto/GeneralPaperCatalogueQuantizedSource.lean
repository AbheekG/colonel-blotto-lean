import Blotto.GeneralPaperCatalogueRationalTrajectory

/-! The actual full source output feeds the actual row-identity-preserving
quantizer. Each field has balanced repeated/zero labels; whole-row budgets
are preserved and the two security losses grow by at most 2/K in total.
This is the proxy-unit semantic join, before original-unit transfer/costs.
-/
namespace Blotto.GeneralPaperCatalogueQuantizedSource
open GeneralPaperComparatorParameters GeneralPaperCatalogueRationalTrajectory GeneralPaperDictionary
set_option autoImplicit false
set_option maxHeartbeats 3500000

def dictionary {m : ℕ} (a : GeneralPaperCodeAlphabet.Alphabet) (k Qv qbar : ℕ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Dictionary (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows m (GeneralPaperScoreScaleParameters.prepare m k).K :=
  GeneralPaperRowQuantizer.buildDivisible (GeneralPaperTrajectoryParameters.rows_positive a.lambda k)
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperTrajectoryParameters.labels_divide_rows m a.lambda k)
    (rows a k Qv qbar weights Bc Br)

theorem paired_security {n : ℕ} (k Qv qbar : ℕ) (hqbar : 0<qbar) (hQv : 0<Qv)
    (weights : FixedArrayTable (n+1) ℕ) (hPositive : ∀ j, 0<weights.read j) (hWeights : ∑ j, weights.read j=Qv)
    (ratio : ℚ) (hr : 0<ratio ∧ ratio≤1) (hCap : ratio.den≤qbar) :
    let a := alphabet (n+1) k qbar hqbar
    let hT := GeneralPaperTrajectoryParameters.rows_positive a.lambda k
    let v := GeneralPaperCatalogueCanonicalGap.normalizedValues Qv hQv weights hPositive hWeights
    security v (ratio:ℝ) (law (dictionary a k Qv qbar weights 1 ratio) hT).law+
      security v 1 (law (dictionary a k Qv qbar weights ratio 1) hT).law≤
        1+3*((GeneralPaperSourceParameters.prepare k).z:ℝ)/32+
          2/((GeneralPaperScoreScaleParameters.prepare (n+1) k).K:ℝ) := by
  dsimp only
  let a := alphabet (n+1) k qbar hqbar
  let v := GeneralPaperCatalogueCanonicalGap.normalizedValues Qv hQv weights hPositive hWeights
  have hA := every_row_feasible a k Qv ratio.den qbar (by omega) hQv weights hWeights 1 ratio
    (by norm_num) (Rat.den_pos ratio) hCap (by simp)
  have hB := every_row_feasible a k Qv ratio.den qbar (by omega) hQv weights hWeights ratio 1
    hr.1.le (Rat.den_pos ratio) hCap (dvd_refl _)
  simp only [Rat.cast_one] at hA
  have hs := (GeneralPaperCataloguePairedSecurity.paper_source k Qv qbar hqbar hQv weights hPositive hWeights ratio hr hCap).2.2
  have hSource : security v (ratio:ℝ) (GeneralPaperCatalogueRationalTrajectory.uniformLaw a k Qv qbar weights 1 ratio).law+
      security v 1 (GeneralPaperCatalogueRationalTrajectory.uniformLaw a k Qv qbar weights ratio 1).law≤1+3*((GeneralPaperSourceParameters.prepare k).z:ℝ)/32 := by
    rw [law_eq a k Qv qbar (by omega) hQv weights hWeights 1 ratio (by norm_num),
      law_eq a k Qv qbar (by omega) hQv weights hWeights ratio 1 hr.1.le]
    exact hs
  exact GeneralPaperRowQuantizer.paired_security_bound (GeneralPaperTrajectoryParameters.rows_positive a.lambda k)
    (GeneralPaperScoreScaleParameters.labels_positive (n+1) k) (GeneralPaperTrajectoryParameters.labels_divide_rows (n+1) a.lambda k)
    (rows a k Qv qbar weights 1 ratio) (rows a k Qv qbar weights ratio 1) 1 (ratio:ℝ) hA hB v
    (by norm_num) (by exact_mod_cast hr.1.le) _ hSource

end Blotto.GeneralPaperCatalogueQuantizedSource
