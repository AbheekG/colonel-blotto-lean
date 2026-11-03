import Blotto.GeneralPaperCachedBitSourcePair
import Blotto.GeneralPaperRationalSourcePairData

/-! The rational streaming front end and retained grid now feed the full
bit-priced source/compiler pair. The front end, grid, two sources and sole
selected compiler each execute once. Full phase/rate calibration remains
separate; downstream arithmetic counters are no longer used here. -/
namespace Blotto.GeneralPaperRationalBitSourcePair
open GeneralPaperProxyParameters GeneralPaperOriginalDrawEquilibrium
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192

def run {m : ℕ} (model : RationalCostModel) (W Wf Wg k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv) (b : ℚ) :
    Option (Columns (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K)×ℕ :=
  let prepared := GeneralPaperRationalSourcePairData.prepare model Wf Wg m k Qv b
  let result := GeneralPaperCachedBitSourcePair.run model W k Qv hQv weights hp hw (b:ℝ) prepared.1
  (result.1,prepared.2+result.2+192*W)

theorem data {m : ℕ} (model : RationalCostModel) (W Wf Wg k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (b : ℚ) (hb : 0<b ∧ b<1) :
    (run model W Wf Wg k Qv hQv weights hp hw b).1=
      (GeneralPaperRationalSourcePairData.run model Wf Wg k Qv hQv weights hp hw b).1 := by
  dsimp only [run,GeneralPaperRationalSourcePairData.run]
  exact GeneralPaperCachedBitSourcePair.data model W k Qv hm hQv weights hp hw (b:ℝ) (by exact_mod_cast hb)
    (GeneralPaperRationalSourcePairData.prepare model Wf Wg m k Qv b).1

theorem actual_return {m : ℕ} (model : RationalCostModel) (W Wf Wg k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hw : ∑ j,weights.read j=Qv)
    (b : ℚ) (hb : 0<b ∧ b<1) :
    ∃ physical pair,(run model W Wf Wg k Qv hQv weights hp hw b).1=some physical ∧
      GeneralPaperSourcePairRun.run k Qv hQv weights hp hw (b:ℝ)=some pair ∧ Matches physical pair ∧
      GeneralPaperSourcePairContract.Contract k Qv hQv weights hp hw (b:ℝ) pair := by
  obtain ⟨physical,pair,hRun,hPair,hMatch,hContract⟩ := GeneralPaperRationalSourcePairData.actual_return model Wf Wg k Qv hm hQv weights hp hw b hb
  exact ⟨physical,pair,(data model W Wf Wg k Qv hm hQv weights hp hw b hb).trans hRun,hPair,hMatch,hContract⟩

end Blotto.GeneralPaperRationalBitSourcePair
