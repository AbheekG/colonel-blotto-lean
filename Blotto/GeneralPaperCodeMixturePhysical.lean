import Blotto.GeneralPaperCodeMixturePayoff
import Blotto.FiniteMixturePayoff
import Blotto.PureBoundaryEquilibria

/-! Canonical whole-allocation laws of decoded finite code mixtures.
Selected physical shifts preserve the exact symbolic budgets. Expected
response payoff equals the finite code game under independent player draws.
-/
namespace Blotto.GeneralPaperCodeMixturePhysical
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCatalogueMixtureOptimizer
set_option autoImplicit false
set_option maxHeartbeats 3500000

def allocation {m : ℕ} {a : Alphabet} {response : Bool} {B : ℚ}
    (law : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a response B) (qbar : ℕ) (l : Fin law.law.labels) : Allocation m :=
  fun j => (((law.choices l).read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C):ℝ)

noncomputable def physicalLaw {m : ℕ} {a : Alphabet} {response : Bool} {B : ℚ}
    (law : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a response B) (qbar : ℕ) : Mixed m :=
  probabilityMixture law.law.weight (fun l => PureBoundaryEquilibria.pointLaw (allocation law qbar l)) law.law.nonnegative law.law.total

theorem allocation_feasible {m : ℕ} (a : Alphabet) (response : Bool) (B : ℚ)
    (law : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a response B)
    (q qbar : ℕ) (hm : 0<m) (hq : 0<q) (hCap : q≤qbar) (hDen : B.den∣q) (l : Fin law.law.labels) :
    Blotto.Feasible (B:ℝ) (allocation law qbar l) := by
  have hd (j : Fin m) : (GeneralPaperCodeDecode.decode a response ((codes law l).read j)).choice=some ((law.choices l).read j) := by
    rw [codes_read]
    exact law.decoded l j
  have hb := (GeneralPaperCatalogueOptimizerBudget.decoded_budget_iff a response q qbar hm hq hCap B hDen
    (codes law l) (law.choices l) hd).mpr (law.budget l)
  apply GeneralPaperCatalogueEpochOutput.rational_feasible B
    (fun j => ((law.choices l).read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C)) _ hb
  intro j
  exact GeneralPaperCatalogueOptimizerBudget.physical_nonnegative _ _
    (GeneralPaperTagBudgetTransfer.shift_positive m qbar a.C hm (by omega) a.scalePositive).le

theorem supported {m : ℕ} (a : Alphabet) (response : Bool) (B : ℚ)
    (law : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a response B)
    (q qbar : ℕ) (hm : 0<m) (hq : 0<q) (hCap : q≤qbar) (hDen : B.den∣q) :
    Supported (B:ℝ) (physicalLaw law qbar) :=
  probabilityMixture_supported _ _ _ _ _ (fun l => PureBoundaryEquilibria.pointLaw_supported _ _
    (allocation_feasible a response B law q qbar hm hq hCap hDen l))

theorem expected_exact {m : ℕ} (a : Alphabet) (responseX responseY : Bool) (BX BY : ℚ)
    (X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a responseX BX)
    (Y : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a responseY BY)
    (qbar : ℕ) (hm : 0<m) (hQ : 0<qbar) (v : Values m) :
    expected v (physicalLaw Y qbar) (physicalLaw X qbar)=
      GeneralPaperFourAverageGap.weightedPayoff v.weight
        (GeneralPaperCodeMixture.marginal X.law) (GeneralPaperCodeMixture.marginal Y.law) := by
  unfold physicalLaw
  rw [expected_probabilityMixture_left]
  simp_rw [expected_probabilityMixture_right]
  rw [GeneralPaperCodeMixturePayoff.weighted_payoff]
  apply Finset.sum_congr rfl
  intro y hy
  apply congrArg (fun value => Y.law.weight y*value)
  apply Finset.sum_congr rfl
  intro x hx
  apply congrArg (fun value => X.law.weight x*value)
  rw [PureBoundaryEquilibria.expected_pointLaw]
  exact GeneralPaperCodePayoff.row_payoff_exact a responseY responseX m qbar hm hQ v
    (fun j => (Y.law.rows y j).val) (fun j => (X.law.rows x j).val)
    (fun j => (Y.choices y).read j) (fun j => (X.choices x).read j) (Y.decoded y) (X.decoded x)

end Blotto.GeneralPaperCodeMixturePhysical
