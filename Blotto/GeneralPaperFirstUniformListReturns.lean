import Blotto.GeneralPaperFirstOriginalExactBitHeadlines
import Blotto.GeneralPaperFirstRealAlgorithmContract

/-! Uniform complete-row list on the actual corrected bit return. Equal
and one-field branches use their separate checked sampling interfaces. -/
namespace Blotto.GeneralPaperFirstUniformListReturns
open GeneralPaperUniformListReturns
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem bit_of_sampling {model : RationalCostModel} {C d K : ℕ}
    (p : GeneralPaperOriginalGameInput.Input) (hOne : GeneralPaperOriginalGameInput.epsilon p < 1)
    (output : GeneralPaperAllBranchBitDispatch.Prepared p.n)
    (hReturn : (GeneralPaperFirstAllBitDispatch.run model K p).1 = some output)
    (hSampling : GeneralPaperFirstOriginalSamplingContract.Contract model C d K p output) : Bit p output := by
  cases hSampling with
  | oneField _ _ _ => trivial
  | equal _ _ _ _ _ => trivial
  | unequal hN hStrict output _ _ =>
    let q := GeneralPaperOriginalGameInput.unequalInput p hStrict
    let actual := GeneralPaperMeasuredUnequalSampling.actual model K q
    have hr : (GeneralPaperFirstAllBitDispatch.run model K p).1 = some (.unequal actual) := by
      rw [GeneralPaperFirstAllBitDispatch.on_unequal model K p hN (ne_of_lt hStrict)]
      rfl
    have he : output = actual := GeneralPaperAllBranchBitDispatch.Prepared.unequal.inj
      (Option.some.inj (hReturn.symm.trans hr))
    subst output
    change Contract _ (GeneralPaperMeasuredUnequalSampling.actual model K q)
    rw [GeneralPaperMeasuredUnequalSampling.data]
    exact at_word model _ q hOne

end Blotto.GeneralPaperFirstUniformListReturns
