import Blotto.GeneralPaperContinuousResponseMixture
import Blotto.RichMinimax

/-! Exact continuous-response representation against every finite feasible
closed candidate law. Original real deviations, zero ties, whole-row joint
probabilities and the canonical independent-player payoff are retained.
-/
namespace Blotto.GeneralPaperContinuousResponsePayoff
open MeasureTheory
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperContinuousResponseMixture GeneralPaperCodeMixturePhysical
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem purePayoff_exact {m : ℕ} (a : Alphabet) (BX B : ℚ) (hB : B≤1) (y : Allocation m) (hy : Blotto.Feasible (B:ℝ) y)
    (X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a false BX) (qbar : ℕ) (hm : 0<m) (hQ : 0<qbar) (v : Values m) :
    purePayoff v y (physicalLaw X qbar)=purePayoff v (physicalRow a B hB y hy qbar) (physicalLaw X qbar) := by
  unfold purePayoff
  apply integral_congr_ae
  apply probabilityMixture_ae X.law.weight (fun l => PureBoundaryEquilibria.pointLaw (allocation X qbar l)) X.law.nonnegative X.law.total
  intro l
  change ∀ᵐ row ∂Measure.dirac (allocation X qbar l), payoff v y row=payoff v (physicalRow a B hB y hy qbar) row
  rw [ae_dirac_eq]
  exact GeneralPaperContinuousResponseMixture.payoff_exact a BX B hB y hy X qbar hm hQ v l

theorem singleton_expected {m : ℕ} (a : Alphabet) (BX B : ℚ) (hB : B≤1) (y : Allocation m) (hy : Blotto.Feasible (B:ℝ) y)
    (X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a false BX) (qbar : ℕ) (v : Values m) :
    expected v (physicalLaw (response a B hB y hy) qbar) (physicalLaw X qbar)=
      purePayoff v (physicalRow a B hB y hy qbar) (physicalLaw X qbar) := by
  calc
    _ = ∑ _l : Fin 1, (1:ℝ)*expected v (PureBoundaryEquilibria.pointLaw (physicalRow a B hB y hy qbar)) (physicalLaw X qbar) :=
      expected_probabilityMixture_left v _ _ _ _ _
    _ = _ := by
      simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,one_mul]
      exact RichMinimax.expected_pointLaw_left v _ _

theorem representation {m : ℕ} (a : Alphabet) (BX B : ℚ) (hB : B≤1) (y : Allocation m) (hy : Blotto.Feasible (B:ℝ) y)
    (X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a false BX) (qbar : ℕ) (hm : 0<m) (hQ : 0<qbar) (v : Values m) :
    ∃ Y : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a true B,
      purePayoff v y (physicalLaw X qbar)=expected v (physicalLaw Y qbar) (physicalLaw X qbar) := by
  refine ⟨response a B hB y hy,?_⟩
  rw [singleton_expected]
  exact purePayoff_exact a BX B hB y hy X qbar hm hQ v

theorem security_le_from_literal {m : ℕ} (a : Alphabet) (BX B : ℚ) (hB : 0≤B) (hOne : B≤1)
    (X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a false BX) (qbar : ℕ) (hm : 0<m) (hQ : 0<qbar) (v : Values m)
    (bound : ℝ) (hBound : ∀ Y : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a true B,
      expected v (physicalLaw Y qbar) (physicalLaw X qbar)≤bound) :
    security v (B:ℝ) (physicalLaw X qbar)≤bound := by
  apply security_le v (by exact_mod_cast hB) _
  intro y hy
  obtain ⟨Y,hY⟩ := representation a BX B hOne y hy X qbar hm hQ v
  rw [hY]
  exact hBound Y

end Blotto.GeneralPaperContinuousResponsePayoff
