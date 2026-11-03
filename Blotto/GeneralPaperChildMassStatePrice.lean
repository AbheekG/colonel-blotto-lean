import Blotto.GeneralPaperQuantileChildPrice

/-! The already-proved native quantile mass certificate supplies both
normality and the sharp exponent range. Callers provide no magnitude or
operand-width premise for either child branch.
-/
namespace Blotto.GeneralPaperChildMassStatePrice
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperGlobalNodeQuery
open GeneralPaperMassApproximation
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

theorem work (right : Bool) (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (ancestor : ℕ) {height : ℕ} (n : Node (height+1)) (storedMass : Number) (hHeight : height+1≤lambda+1)
    (hValid : Valid lambda k n) (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor n)
    (hMass : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
      (trueMass k ancestor n) storedMass) :
    (GeneralPaperQuantileChildPrice.run right primitive W c ancestor n storedMass).2≤
      1048576*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)*
        (W+primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := by
  have hn : Normal c.powers.format.unit storedMass := by rw [hc]; exact hMass.1
  have hRange := GeneralPaperTreeMassRange.true_range k (GeneralPaperPowerPrecision.levelBound lambda k) ancestor n hPath
  have hCap := GeneralPaperMassExponentRange.paper_range lambda k _ _ (height+1) _ storedMass hHeight
    (by unfold budget; omega) hMass (Or.inr hRange.1) hRange.2
  exact GeneralPaperQuantileChildPrice.work right primitive hMono W m lambda k Qv c hc ancestor n storedMass
    hHeight hValid hPath hn hCap

theorem certificate (right : Bool) (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (ancestor : ℕ) {height : ℕ} (n : Node (height+1)) (storedMass : Number) (hHeight : height+1≤lambda+1)
    (hValid : Valid lambda k n) (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor n)
    (hMass : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
      (trueMass k ancestor n) storedMass) :
    let child := if right then rightChild n else leftChild n
    Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
      (trueMass k (ancestor+offset n) child)
      (GeneralPaperQuantileChildPrice.run right primitive W c ancestor n storedMass).1.number := by
  rw [GeneralPaperQuantileChildPrice.data right primitive W m lambda k Qv c hc ancestor n storedMass hValid hPath,hc]
  cases right
  · exact GeneralPaperQuantileChildMass.left_bound lambda k ancestor n storedMass hHeight hValid hPath hMass
  · exact GeneralPaperQuantileChildMass.right_bound lambda k ancestor n storedMass hHeight hValid hPath hMass

theorem magnitude (right : Bool) (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (ancestor : ℕ) {height : ℕ} (n : Node (height+1)) (storedMass : Number) (hHeight : height+1≤lambda+1)
    (hValid : Valid lambda k n) (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor n)
    (hMass : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
      (trueMass k ancestor n) storedMass) :
    (GeneralPaperQuantileChildPrice.run right primitive W c ancestor n storedMass).1.number.exponent.natAbs≤
      GeneralPaperQuantileExponentRange.cap lambda k := by
  have hb := certificate right primitive W m lambda k Qv c hc ancestor n storedMass hHeight hValid hPath hMass
  have hp := child_paths _ ancestor n hPath
  cases right
  · have hr := GeneralPaperTreeMassRange.true_range k (GeneralPaperPowerPrecision.levelBound lambda k)
      (ancestor+offset n) (leftChild n) hp.1
    exact GeneralPaperMassExponentRange.paper_range lambda k _ _ height _ _ (by omega)
      (by unfold budget; omega) hb (Or.inr hr.1) hr.2
  · have hr := GeneralPaperTreeMassRange.true_range k (GeneralPaperPowerPrecision.levelBound lambda k)
      (ancestor+offset n) (rightChild n) hp.2
    exact GeneralPaperMassExponentRange.paper_range lambda k _ _ height _ _ (by omega)
      (by unfold budget; omega) hb (Or.inr hr.1) hr.2

end Blotto.GeneralPaperChildMassStatePrice
