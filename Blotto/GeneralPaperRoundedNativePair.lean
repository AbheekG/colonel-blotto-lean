import Blotto.GeneralPaperRationalSourcePairData

/-! Native value rounding followed by the actual rational-input physical
source/compiler pair. Every preparation executes once. Matching the
canonical selected pair is a proved return postcondition. The complete
bit/asymptotic/working-space price of this composition is still separate. -/
namespace Blotto.GeneralPaperRoundedNativePair
open GeneralPaperOriginalDrawEquilibrium
set_option autoImplicit false
set_option maxHeartbeats 4500000

def run {m : ℕ} (valueBits : Bool) (model : RationalCostModel) (Wv Wf Wg k : ℕ)
    (values : FixedArrayTable m ℚ) (v : RationalFieldSelector m) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) :
    Option (Columns (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows
      m (GeneralPaperProxyParameters.prepare m k).K)×ℕ :=
  let rounded := GeneralPaperValueRoundingPaperContract.run valueBits model Wv 512 k values
  let hp := GeneralPaperValueRoundingPaperContract.positivity valueBits model Wv 512 k (by decide) values v hv
  let pair := GeneralPaperRationalSourcePairData.run model Wf Wg k rounded.1.2 hp.1 rounded.1.1 hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum valueBits model Wv 512 k values) b
  (pair.1,rounded.2+pair.2+64)

theorem data {m : ℕ} (valueBits : Bool) (model : RationalCostModel) (Wv Wf Wg k : ℕ)
    (values : FixedArrayTable m ℚ) (v : RationalFieldSelector m) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) :
    (run valueBits model Wv Wf Wg k values v hv b).1.map GeneralPaperPhysicalColumnPair.decode=
      GeneralPaperRoundedValueCanonical.run valueBits model Wv k values v hv (b:ℝ) := by
  let rounded := GeneralPaperValueRoundingPaperContract.run valueBits model Wv 512 k values
  have hp := GeneralPaperValueRoundingPaperContract.positivity valueBits model Wv 512 k (by decide) values v hv
  dsimp only [run,GeneralPaperRoundedValueCanonical.run]
  exact GeneralPaperRationalSourcePairData.data model Wf Wg k rounded.1.2 v.fields_positive hp.1 rounded.1.1 hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum valueBits model Wv 512 k values) b hb

theorem return_of_canonical {m : ℕ} (valueBits : Bool) (model : RationalCostModel) (Wv Wf Wg k : ℕ)
    (values : FixedArrayTable m ℚ) (v : RationalFieldSelector m) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1)
    (pair : GeneralPaperSourcePairRun.Pair
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows m (GeneralPaperProxyParameters.prepare m k).K)
    (hPair : GeneralPaperRoundedValueCanonical.run valueBits model Wv k values v hv (b:ℝ)=some pair) :
    ∃ physical,(run valueBits model Wv Wf Wg k values v hv b).1=some physical ∧ Matches physical pair := by
  have hd := data valueBits model Wv Wf Wg k values v hv b hb
  erw [hPair] at hd
  obtain ⟨physical,hRun,hDecode⟩ := Option.map_eq_some_iff.mp hd
  exact ⟨physical,hRun,(GeneralPaperPhysicalColumnPair.matches_iff physical pair).mpr hDecode⟩

end Blotto.GeneralPaperRoundedNativePair
