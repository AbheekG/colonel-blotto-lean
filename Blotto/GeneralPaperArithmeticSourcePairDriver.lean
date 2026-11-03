import Blotto.GeneralPaperArithmeticPairPreparation

/-! Complete deterministic arithmetic source/compiler pair data path.
Preparation/classification/materialization run once, then the two full
sources and selected compiler return physical columns. Matches is proved
from those returns. Complete asymptotic/bit/space/fair-bit joins remain. -/
namespace Blotto.GeneralPaperArithmeticSourcePairDriver
open GeneralPaperOriginalDrawEquilibrium
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4500000

noncomputable def run {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv) (b : ℝ) :
    Option (Columns (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows
      m (GeneralPaperProxyParameters.prepare m k).K)×ℕ :=
  let prepared := GeneralPaperArithmeticPairPreparation.run m k Qv b
  let result := GeneralPaperCachedSourcePair.run model k Qv hQv weights hp hw b prepared.1
  (result.1,prepared.2+result.2+64)

theorem data {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) :
    (run model k Qv hQv weights hp hw b).1.map GeneralPaperPhysicalColumnPair.decode=
      GeneralPaperSourcePairRun.run k Qv hQv weights hp hw b := by
  dsimp only [run]
  exact (GeneralPaperCachedSourcePairLaw.data model k Qv hm hQv weights hp hw b hb
    (GeneralPaperArithmeticPairPreparation.run m k Qv b).1).trans
    (GeneralPaperCheckedSourcePair.run_eq k Qv hm hQv weights hp hw b hb)

theorem actual_return {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) :
    ∃ physical pair,(run model k Qv hQv weights hp hw b).1=some physical ∧
      GeneralPaperSourcePairRun.run k Qv hQv weights hp hw b=some pair ∧ Matches physical pair ∧
      GeneralPaperSourcePairContract.Contract k Qv hQv weights hp hw b pair := by
  dsimp only [run]
  exact GeneralPaperCachedSourcePairLaw.actual_return model k Qv hm hQv weights hp hw b hb
    (GeneralPaperArithmeticPairPreparation.run m k Qv b).1

end Blotto.GeneralPaperArithmeticSourcePairDriver
