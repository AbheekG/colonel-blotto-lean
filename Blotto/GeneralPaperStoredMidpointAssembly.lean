import Blotto.GeneralPaperStoredPreparedRead

/-! Rational assembly receives the actually loaded midpoint count. It does
not compute a denominator power or receive a source prepared cache. -/
namespace Blotto.GeneralPaperStoredMidpointAssembly
open GeneralPaperRationalScalarStep
set_option autoImplicit false

def run (model : RationalCostModel) (A count rank : ℕ) : ℚ × ℕ :=
  let index := natural A rank
  let retained := natural A count
  let doubled := GeneralPaperRationalScalarStep.run model A .mul index.1 2
  let numerator := GeneralPaperRationalScalarStep.run model A .add doubled.1 1
  let denominator := GeneralPaperRationalScalarStep.run model A .mul 2 retained.1
  let quotient := GeneralPaperRationalScalarStep.run model A .div numerator.1 denominator.1
  (quotient.1,index.2 + retained.2 + doubled.2 + numerator.2 + denominator.2 + quotient.2)

theorem eq_cached {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (prepared : GeneralPaperEqualPreparedCache.Prepared G l) (model : RationalCostModel) (A rank : ℕ) :
    run model A prepared.midpointCount rank = GeneralPaperCachedMidpointAssembly.run prepared model A rank := rfl

theorem source {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (prepared : GeneralPaperEqualPreparedCache.Prepared G l) (model : RationalCostModel) (A : ℕ)
    (fresh : Fin prepared.midpointBits → Bool) :
    (run model A prepared.midpointCount (balancedBitIndex prepared.midpointBits fresh).val).1 =
      GeneralPaperEqualPreparedCache.midpoint prepared fresh := GeneralPaperCachedMidpointAssembly.data prepared model A fresh

theorem work {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (prepared : GeneralPaperEqualPreparedCache.Prepared G l) (model : RationalCostModel) (A rank : ℕ)
    (hRank : rank < 2 ^ prepared.midpointBits) :
    (run model A prepared.midpointCount rank).2 ≤
      24 * model.rat (1 + 2 * GeneralPaperCachedMidpointAssembly.height prepared.midpointBits) + 96 * A + 96 :=
  GeneralPaperCachedMidpointAssembly.work prepared model A rank hRank

end Blotto.GeneralPaperStoredMidpointAssembly
