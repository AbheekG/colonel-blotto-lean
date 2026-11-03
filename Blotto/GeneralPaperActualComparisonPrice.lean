import Blotto.GeneralPaperQuantileComparisonPrice

/-! Comparison joins at a reached descent state and at the actual returned
preparation cache. These are erased propositions about existing results;
their state expressions introduce no repeated preparation or tree traversal.
-/
namespace Blotto.GeneralPaperActualComparisonPrice
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperIntervalLevels
open GeneralPaperGlobalNodeQuery GeneralPaperMassApproximation
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem descent_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv j height ancestor : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (node : Node (height+1)) (total storedMass storedPrefix : Number)
    (hJ : j≤(GeneralPaperSourceParameters.prepare k).summarySize) (hHeight : height+1≤lambda+1)
    (hValid : Valid lambda k node) (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (hMass : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
      (trueMass k ancestor node) storedMass)
    (hTotal : Normal (GeneralPaperPreparedPowers.prepare lambda k).format.unit total)
    (hPrefix : Normal (GeneralPaperPreparedPowers.prepare lambda k).format.unit storedPrefix)
    (hSafe : GeneralPaperQuantileExponentRange.Safe lambda k (GeneralPaperQuantileComparison.width lambda k) j
      (GeneralPaperSourceParameters.prepare k).summarySize total (height+1) node ancestor storedMass storedPrefix) :
    let prepared := GeneralPaperPreparedPowers.prepare lambda k
    let left := GeneralPaperQuantileDescent.leftMass prepared ancestor node storedMass
    let through := GeneralPaperDyadicAddition.add prepared.format.unit prepared.format.fractionalBits storedPrefix left.number
    (GeneralPaperQuantileComparisonPrice.run primitive W (GeneralPaperQuantileComparison.width lambda k) c j total through.number).2≤
      1048576*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)*
        (W+primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := by
  let prepared := GeneralPaperPreparedPowers.prepare lambda k
  let left := GeneralPaperQuantileDescent.leftMass prepared ancestor node storedMass
  let through := GeneralPaperDyadicAddition.add prepared.format.unit prepared.format.fractionalBits storedPrefix left.number
  have hl := GeneralPaperQuantileChildMass.left_bound lambda k ancestor node storedMass hHeight hValid hPath hMass
  have ht : Normal prepared.format.unit through.number :=
    GeneralPaperDyadicAddition.add_normal prepared.format.unit prepared.format.fractionalBits
      (GeneralPaperPowerPrecision.unit_positive lambda k) (GeneralPaperPowerPrecision.unit_power lambda k)
      storedPrefix left.number hPrefix hl.1
  change GeneralPaperQuantileExponentRange.StateBound _ _ _ _ ∧ _ ∧ _ ∧
    through.number.exponent.natAbs≤_ ∧ _ at hSafe
  apply GeneralPaperQuantileComparisonPrice.work primitive hMono W m lambda k Qv _ c hc rfl j total through.number
  · rw [hc]; exact hJ
  · rw [hc]; exact hTotal
  · rw [hc]; exact ht
  · exact hSafe.1.1
  · exact hSafe.2.2.2.1

theorem branches (primitive : ℕ → ℕ) (W m lambda k Qv digits j prefixExponent totalExponent : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k)
    (storedPrefix storedTotal : Number) (P T : ℚ)
    (hJ : j≤(GeneralPaperSourceParameters.prepare k).summarySize) (hT : 0<T) (hPT : P≤T)
    (hPE : prefixExponent≤budget lambda k) (hTE : totalExponent≤budget lambda k)
    (hPrefix : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit prefixExponent P storedPrefix)
    (hTotal : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit totalExponent T storedTotal) :
    ((GeneralPaperQuantileComparisonPrice.run primitive W digits c j storedTotal storedPrefix).1.answer=true →
      (j:ℚ)/(GeneralPaperSourceParameters.prepare k).summarySize-GeneralPaperNormalizedMassError.delta k≤P/T) ∧
    ((GeneralPaperQuantileComparisonPrice.run primitive W digits c j storedTotal storedPrefix).1.answer=false →
      P/T≤(j:ℚ)/(GeneralPaperSourceParameters.prepare k).summarySize+GeneralPaperNormalizedMassError.delta k) := by
  rw [GeneralPaperQuantileComparisonPrice.data primitive W m lambda k Qv digits c hc hDigits]
  exact GeneralPaperQuantileComparison.choose_branches lambda k j prefixExponent totalExponent
    storedPrefix storedTotal P T hJ hT hPT hPE hTE hPrefix hTotal

theorem prepared_work {m : ℕ} (model : RationalCostModel) (W k Qv j : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (total storedPrefix : Number)
    (hJ : j≤(GeneralPaperSourceParameters.prepare k).summarySize)
    (hTotal : Normal (GeneralPaperPowerPrecision.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).unit total)
    (hPrefix : Normal (GeneralPaperPowerPrecision.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).unit storedPrefix)
    (hTotalCap : total.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap (GeneralPaperProxyParameters.alphabet m k).lambda k)
    (hPrefixCap : storedPrefix.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap (GeneralPaperProxyParameters.alphabet m k).lambda k) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    (GeneralPaperQuantileComparisonPrice.run model.rat W ready.1.2.wordWidth ready.2.source j total storedPrefix).2≤
      1048576*(GeneralPaperSourcePreparationSizes.measure m a.lambda k Qv+1)*
        (W+model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m a.lambda k Qv)) := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact GeneralPaperQuantileComparisonPrice.work model.rat model.monotone W m
    (GeneralPaperProxyParameters.alphabet m k).lambda k Qv _ _ rfl rfl j total storedPrefix
    hJ hTotal hPrefix hTotalCap hPrefixCap

theorem prepared_same_data {m : ℕ} (model : RationalCostModel) (W k Qv j : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (total storedPrefix : Number) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    (GeneralPaperQuantileComparisonPrice.run model.rat W ready.1.2.wordWidth ready.2.source j total storedPrefix).1=
      (GeneralPaperQuantileComparisonPrice.arithmetic ready.1.2.wordWidth ready.2.source j total storedPrefix).1 := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact GeneralPaperQuantileComparisonPrice.same_data model.rat W m
    (GeneralPaperProxyParameters.alphabet m k).lambda k Qv _ _ rfl rfl j total storedPrefix

end Blotto.GeneralPaperActualComparisonPrice
