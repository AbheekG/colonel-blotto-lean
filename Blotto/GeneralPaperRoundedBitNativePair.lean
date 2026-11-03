import Blotto.GeneralPaperRationalBitSourcePair
import Blotto.GeneralPaperRoundedNativePair

/-! Bit-priced native value rounding followed by the complete rational
bit source/compiler pair. Its actual physical arrays equal the previously
verified rounded compiler arrays, with no supplied matching premise. -/
namespace Blotto.GeneralPaperRoundedBitNativePair
open GeneralPaperOriginalDrawEquilibrium
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192

def run {m : ℕ} (model : RationalCostModel) (W Wv Wf Wg k : ℕ)
    (values : FixedArrayTable m ℚ) (v : RationalFieldSelector m) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) :
    Option (Columns (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows
      m (GeneralPaperProxyParameters.prepare m k).K)×ℕ :=
  let rounded := GeneralPaperValueRoundingPaperContract.run true model Wv 512 k values
  let hp := GeneralPaperValueRoundingPaperContract.positivity true model Wv 512 k (by decide) values v hv
  let pair := GeneralPaperRationalBitSourcePair.run model W Wf Wg k rounded.1.2 hp.1 rounded.1.1 hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum true model Wv 512 k values) b
  (pair.1,rounded.2+pair.2+64*W)

theorem data {m : ℕ} (model : RationalCostModel) (W Wv Wf Wg k : ℕ)
    (values : FixedArrayTable m ℚ) (v : RationalFieldSelector m) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) :
    (run model W Wv Wf Wg k values v hv b).1=(GeneralPaperRoundedNativePair.run true model Wv Wf Wg k values v hv b).1 := by
  let rounded := GeneralPaperValueRoundingPaperContract.run true model Wv 512 k values
  have hp := GeneralPaperValueRoundingPaperContract.positivity true model Wv 512 k (by decide) values v hv
  dsimp only [run,GeneralPaperRoundedNativePair.run]
  exact GeneralPaperRationalBitSourcePair.data model W Wf Wg k rounded.1.2 v.fields_positive hp.1 rounded.1.1 hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum true model Wv 512 k values) b hb

theorem return_of_canonical {m : ℕ} (model : RationalCostModel) (W Wv Wf Wg k : ℕ)
    (values : FixedArrayTable m ℚ) (v : RationalFieldSelector m) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1)
    (pair : GeneralPaperSourcePairRun.Pair
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows m (GeneralPaperProxyParameters.prepare m k).K)
    (hPair : GeneralPaperRoundedValueCanonical.run true model Wv k values v hv (b:ℝ)=some pair) :
    ∃ physical,(run model W Wv Wf Wg k values v hv b).1=some physical ∧ Matches physical pair := by
  obtain ⟨physical,hRun,hMatches⟩ := GeneralPaperRoundedNativePair.return_of_canonical true model Wv Wf Wg k values v hv b hb pair hPair
  exact ⟨physical,(data model W Wv Wf Wg k values v hv b hb).trans hRun,hMatches⟩

end Blotto.GeneralPaperRoundedBitNativePair
