import Blotto.GeneralPaperActualAdditionPrice

/-! A descent step computes the left mass, through-prefix and comparison
once and returns those three records by reference. The actual state supplies
every normality/range premise. Recursive control/path construction follows
this step and is a separate remaining join.
-/
namespace Blotto.GeneralPaperQuantileStepPrice
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperIntervalLevels
open GeneralPaperGlobalNodeQuery GeneralPaperMassApproximation
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

structure Step where
  left : GeneralPaperDyadicMultiply.Result
  through : GeneralPaperDyadicMultiply.Result
  comparison : GeneralPaperDyadicCompare.Result

def specification (c : GeneralPaperMaterializedPowerCache.Cache) (digits j ancestor : ℕ)
    {height : ℕ} (node : Node (height+1)) (total storedMass storedPrefix : Number) : Step :=
  let left := GeneralPaperQuantileDescent.leftMass c.powers ancestor node storedMass
  let through := GeneralPaperDyadicAddition.add c.powers.format.unit c.powers.format.fractionalBits storedPrefix left.number
  let comparison := GeneralPaperDyadicCompare.scaledLE digits j total c.controls.source.summarySize through.number
  ⟨left,through,comparison⟩

def run (primitive : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache) (digits j ancestor : ℕ)
    {height : ℕ} (node : Node (height+1)) (total storedMass storedPrefix : Number) : Step × ℕ :=
  let left := GeneralPaperQuantileChildPrice.run false primitive W c ancestor node storedMass
  let through := GeneralPaperQuantileAdditionPrice.run primitive W c storedPrefix left.1.number
  let comparison := GeneralPaperQuantileComparisonPrice.run primitive W digits c j total through.1.number
  (⟨left.1,through.1,comparison.1⟩,left.2+through.2+comparison.2+96*W)

def arithmetic (c : GeneralPaperMaterializedPowerCache.Cache) (digits j ancestor : ℕ)
    {height : ℕ} (node : Node (height+1)) (total storedMass storedPrefix : Number) : Step × ℕ :=
  let left := GeneralPaperQuantileChildPrice.arithmetic false c ancestor node storedMass
  let through := GeneralPaperQuantileAdditionPrice.arithmetic c storedPrefix left.1.number
  let comparison := GeneralPaperQuantileComparisonPrice.arithmetic digits c j total through.1.number
  (⟨left.1,through.1,comparison.1⟩,left.2+through.2+comparison.2+96)

theorem data (primitive : ℕ → ℕ) (W m lambda k Qv digits j ancestor : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    {height : ℕ} (node : Node (height+1)) (total storedMass storedPrefix : Number)
    (hHeight : height+1≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (hMass : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
      (trueMass k ancestor node) storedMass) (hPrefix : Normal c.powers.format.unit storedPrefix) :
    (run primitive W c digits j ancestor node total storedMass storedPrefix).1=
      specification c digits j ancestor node total storedMass storedPrefix := by
  let left := GeneralPaperQuantileChildPrice.run false primitive W c ancestor node storedMass
  have hd := GeneralPaperQuantileChildPrice.data false primitive W m lambda k Qv c hc ancestor node storedMass hValid hPath
  simp only [Bool.false_eq_true,ite_false] at hd
  have hl := GeneralPaperQuantileChildMass.left_bound lambda k ancestor node storedMass hHeight hValid hPath hMass
  have hn : Normal c.powers.format.unit left.1.number := by rw [hd,hc]; exact hl.1
  have ha := GeneralPaperQuantileAdditionPrice.data primitive W m lambda k Qv c hc storedPrefix left.1.number hPrefix hn
  unfold run
  dsimp only
  simp only [GeneralPaperQuantileComparisonPrice.run,GeneralPaperScaledComparisonPrice.data]
  rw [ha,hd]
  rfl

theorem arithmetic_data (m lambda k Qv digits j ancestor : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    {height : ℕ} (node : Node (height+1)) (total storedMass storedPrefix : Number)
    (hHeight : height+1≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (hMass : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
      (trueMass k ancestor node) storedMass) (hPrefix : Normal c.powers.format.unit storedPrefix) :
    (arithmetic c digits j ancestor node total storedMass storedPrefix).1=
      specification c digits j ancestor node total storedMass storedPrefix := by
  let left := GeneralPaperQuantileChildPrice.arithmetic false c ancestor node storedMass
  have hd := GeneralPaperQuantileChildPrice.arithmetic_data false c ancestor node storedMass
  simp only [Bool.false_eq_true,ite_false] at hd
  have hl := GeneralPaperQuantileChildMass.left_bound lambda k ancestor node storedMass hHeight hValid hPath hMass
  have hn : Normal c.powers.format.unit left.1.number := by rw [hd,hc]; exact hl.1
  have ha := GeneralPaperQuantileAdditionPrice.arithmetic_data m lambda k Qv c hc storedPrefix left.1.number hPrefix hn
  unfold arithmetic
  dsimp only
  simp only [GeneralPaperQuantileComparisonPrice.arithmetic,GeneralPaperScaledComparisonPrice.arithmetic_data]
  rw [ha,hd]
  rfl

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv digits j ancestor : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k)
    {height : ℕ} (node : Node (height+1)) (total storedMass storedPrefix : Number)
    (hJ : j≤(GeneralPaperSourceParameters.prepare k).summarySize) (hHeight : height+1≤lambda+1)
    (hValid : Valid lambda k node) (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (hMass : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
      (trueMass k ancestor node) storedMass)
    (hTotal : Normal (GeneralPaperPreparedPowers.prepare lambda k).format.unit total)
    (hPrefix : Normal (GeneralPaperPreparedPowers.prepare lambda k).format.unit storedPrefix)
    (hSafe : GeneralPaperQuantileExponentRange.Safe lambda k digits j (GeneralPaperSourceParameters.prepare k).summarySize
      total (height+1) node ancestor storedMass storedPrefix) :
    (run primitive W c digits j ancestor node total storedMass storedPrefix).2≤
      4194304*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)*
        (W+primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := by
  let left := GeneralPaperQuantileChildPrice.run false primitive W c ancestor node storedMass
  let through := GeneralPaperQuantileAdditionPrice.run primitive W c storedPrefix left.1.number
  have hd := GeneralPaperQuantileChildPrice.data false primitive W m lambda k Qv c hc ancestor node storedMass hValid hPath
  simp only [Bool.false_eq_true,ite_false] at hd
  have hlc := GeneralPaperQuantileChildMass.left_bound lambda k ancestor node storedMass hHeight hValid hPath hMass
  have hln : Normal c.powers.format.unit left.1.number := by rw [hd,hc]; exact hlc.1
  have hpn : Normal c.powers.format.unit storedPrefix := by rw [hc]; exact hPrefix
  have ha := GeneralPaperQuantileAdditionPrice.data primitive W m lambda k Qv c hc storedPrefix left.1.number hpn hln
  have hm := GeneralPaperChildMassStatePrice.work false primitive hMono W m lambda k Qv c hc ancestor node storedMass
    hHeight hValid hPath hMass
  have hAdd := GeneralPaperActualAdditionPrice.descent_work primitive hMono W m lambda k Qv digits j _ height ancestor c hc
    node total storedMass storedPrefix hHeight hValid hPath hMass hPrefix hSafe
  have hCmpSafe := hSafe
  rw [hDigits] at hCmpSafe
  have hCmp := GeneralPaperActualComparisonPrice.descent_work primitive hMono W m lambda k Qv j height ancestor c hc
    node total storedMass storedPrefix hJ hHeight hValid hPath hMass hTotal hPrefix hCmpSafe
  have hAdd' : through.2≤524288*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)*
      (W+primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := by
    dsimp only [through]
    rw [hd,hc]
    rw [hc] at hAdd
    exact hAdd
  have hCmp' : (GeneralPaperQuantileComparisonPrice.run primitive W digits c j total through.1.number).2≤
      1048576*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)*
        (W+primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := by
    dsimp only [through]
    rw [ha,hd,hDigits,hc]
    rw [hc] at hCmp
    exact hCmp
  change left.2+through.2+
    (GeneralPaperQuantileComparisonPrice.run primitive W digits c j total through.1.number).2+96*W≤_
  nlinarith only [hm,hAdd',hCmp',Nat.zero_le (GeneralPaperSourcePreparationSizes.measure m lambda k Qv),
    Nat.zero_le (primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv))]

theorem arithmetic_work (m lambda k Qv digits j ancestor : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k)
    {height : ℕ} (node : Node (height+1)) (total storedMass storedPrefix : Number) :
    (arithmetic c digits j ancestor node total storedMass storedPrefix).2≤
      4194304*(GeneralPaperSourcePreparationSizes.measure m lambda k Qv+1)^2 := by
  let left := GeneralPaperQuantileChildPrice.arithmetic false c ancestor node storedMass
  let through := GeneralPaperQuantileAdditionPrice.arithmetic c storedPrefix left.1.number
  have hl := GeneralPaperQuantileChildPrice.arithmetic_work false m lambda k Qv c hc ancestor node storedMass
  have ha := GeneralPaperQuantileAdditionPrice.arithmetic_work m lambda k Qv c hc storedPrefix left.1.number
  have hc := GeneralPaperQuantileComparisonPrice.arithmetic_work m lambda k Qv digits c hDigits j total through.1.number
  change left.2+through.2+(GeneralPaperQuantileComparisonPrice.arithmetic digits c j total through.1.number).2+96≤_
  nlinarith only [hl,ha,hc,Nat.zero_le (GeneralPaperSourcePreparationSizes.measure m lambda k Qv)]

end Blotto.GeneralPaperQuantileStepPrice
