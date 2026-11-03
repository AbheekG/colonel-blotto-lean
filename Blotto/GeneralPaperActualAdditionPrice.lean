import Blotto.GeneralPaperQuantileAdditionPrice

/-! The actual left-child certificate and erased quantile invariant supply
all addition inputs. The through-prefix certificate retains the native
error budget. Returned preparation caches supply the format without replay.
-/
namespace Blotto.GeneralPaperActualAdditionPrice
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperIntervalLevels
open GeneralPaperGlobalNodeQuery GeneralPaperMassApproximation
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem descent_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv width j s height ancestor : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (node : Node (height+1)) (total storedMass storedPrefix : Number)
    (hHeight : height+1≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (hMass : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
      (trueMass k ancestor node) storedMass)
    (hPrefix : Normal (GeneralPaperPreparedPowers.prepare lambda k).format.unit storedPrefix)
    (hSafe : GeneralPaperQuantileExponentRange.Safe lambda k width j s total (height+1) node ancestor storedMass storedPrefix) :
    let left := GeneralPaperQuantileDescent.leftMass (GeneralPaperPreparedPowers.prepare lambda k) ancestor node storedMass
    (GeneralPaperQuantileAdditionPrice.run primitive W c storedPrefix left.number).2≤
      524288*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)*
        (W+primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := by
  have hl := GeneralPaperQuantileChildMass.left_bound lambda k ancestor node storedMass hHeight hValid hPath hMass
  change GeneralPaperQuantileExponentRange.StateBound _ _ _ _ ∧ _ ∧ _ ∧ _ ∧ _ at hSafe
  apply GeneralPaperQuantileAdditionPrice.work primitive hMono W m lambda k Qv c hc _ _
  · rw [hc]; exact hPrefix
  · rw [hc]; exact hl.1
  · exact hSafe.1.2.2
  · exact hSafe.2.1

theorem descent_certificate (primitive : ℕ → ℕ) (W m lambda k Qv height ancestor depth : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (node : Node (height+1)) (storedMass storedPrefix : Number) (P : ℚ)
    (hHeight : height+1≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (hMass : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
      (trueMass k ancestor node) storedMass)
    (hPrefix : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k+depth) P storedPrefix) :
    let left := GeneralPaperQuantileDescent.leftMass (GeneralPaperPreparedPowers.prepare lambda k) ancestor node storedMass
    Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k+(depth+1))
      (P+trueMass k (ancestor+offset node) (leftChild node))
      (GeneralPaperQuantileAdditionPrice.run primitive W c storedPrefix left.number).1.number := by
  dsimp only
  have hl := GeneralPaperQuantileChildMass.left_bound lambda k ancestor node storedMass hHeight hValid hPath hMass
  have hp : Normal c.powers.format.unit storedPrefix := by rw [hc]; exact hPrefix.1
  have hln : Normal c.powers.format.unit
      (GeneralPaperQuantileDescent.leftMass (GeneralPaperPreparedPowers.prepare lambda k) ancestor node storedMass).number := by
    rw [hc]; exact hl.1
  rw [GeneralPaperQuantileAdditionPrice.data primitive W m lambda k Qv c hc _ _ hp hln,hc]
  have hlw := weaken _ _ (queryExponent lambda k+depth) _ _ (GeneralPaperPowerPrecision.unit_positive lambda k)
    (Nat.le_add_right _ _) hl
  simpa only [Nat.add_assoc,GeneralPaperMaterializedPowerCache.specification,GeneralPaperPreparedPowers.prepare]
    using add_bound _ _ _ (GeneralPaperPowerPrecision.unit_positive lambda k)
    (GeneralPaperPowerPrecision.unit_power lambda k) P _ storedPrefix _ hPrefix hlw

theorem prepared_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (left right : Number)
    (hLeft : Normal (GeneralPaperPowerPrecision.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).unit left)
    (hRight : Normal (GeneralPaperPowerPrecision.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).unit right)
    (hLeftCap : left.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap (GeneralPaperProxyParameters.alphabet m k).lambda k)
    (hRightCap : right.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap (GeneralPaperProxyParameters.alphabet m k).lambda k) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    (GeneralPaperQuantileAdditionPrice.run model.rat W ready.2.source left right).2≤
      524288*(GeneralPaperSourcePreparationSizes.measure m a.lambda k Qv+1)*
        (W+model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m a.lambda k Qv)) := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact GeneralPaperQuantileAdditionPrice.work model.rat model.monotone W m
    (GeneralPaperProxyParameters.alphabet m k).lambda k Qv _ rfl left right hLeft hRight hLeftCap hRightCap

theorem prepared_same_data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (left right : Number)
    (hLeft : Normal (GeneralPaperPowerPrecision.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).unit left)
    (hRight : Normal (GeneralPaperPowerPrecision.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).unit right) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    (GeneralPaperQuantileAdditionPrice.run model.rat W ready.2.source left right).1=
      (GeneralPaperQuantileAdditionPrice.arithmetic ready.2.source left right).1 := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact GeneralPaperQuantileAdditionPrice.same_data model.rat W m
    (GeneralPaperProxyParameters.alphabet m k).lambda k Qv _ rfl left right hLeft hRight

end Blotto.GeneralPaperActualAdditionPrice
