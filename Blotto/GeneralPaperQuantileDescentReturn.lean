import Blotto.GeneralPaperQuantileDescentArithmetic

/-! The existing native annotation theorem supplies all return metadata
caps at actual recursive children. No caller chooses a work/visit capacity.
-/
namespace Blotto.GeneralPaperQuantileDescentReturn
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperIntervalLevels
open GeneralPaperQuantileDescentExecution GeneralPaperMassApproximation GeneralPaperGlobalNodeQuery
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem local_work (lambda k digits j s ancestor : ℕ) {height : ℕ} (node : Node (height+1))
    (total storedMass storedPrefix : Number) :
    let p := GeneralPaperPreparedPowers.prepare lambda k
    let left := GeneralPaperQuantileDescent.leftMass p ancestor node storedMass
    let right := GeneralPaperQuantileDescent.rightMass p ancestor node storedMass
    let through := GeneralPaperDyadicAddition.add p.format.unit p.format.fractionalBits storedPrefix left.number
    let comp := GeneralPaperDyadicCompare.scaledLE digits j total s through.number
    left.work+right.work+through.work+comp.work+24≤GeneralPaperQuantileWork.stepPrice lambda k digits := by
  have hm := GeneralPaperQuantileWork.child_work lambda k ancestor node storedMass
  have ha := GeneralPaperDyadicAddition.add_work
    (GeneralPaperPreparedPowers.prepare lambda k).format.unit (GeneralPaperPreparedPowers.prepare lambda k).format.fractionalBits
    storedPrefix (GeneralPaperQuantileDescent.leftMass (GeneralPaperPreparedPowers.prepare lambda k) ancestor node storedMass).number
  have hc := GeneralPaperDyadicCompare.scaled_work digits j total s
    (GeneralPaperDyadicAddition.add (GeneralPaperPreparedPowers.prepare lambda k).format.unit
      (GeneralPaperPreparedPowers.prepare lambda k).format.fractionalBits storedPrefix
      (GeneralPaperQuantileDescent.leftMass (GeneralPaperPreparedPowers.prepare lambda k) ancestor node storedMass).number).number
  dsimp only
  unfold GeneralPaperQuantileWork.stepPrice
  omega

theorem work (bits : Bool) (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv digits j : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (total : Number)
    (height : ℕ) (node : Node height) (ancestor : ℕ) (storedMass storedPrefix : Number)
    (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (hMass : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
      (trueMass k ancestor node) storedMass)
    (hPrefix : Normal (GeneralPaperPreparedPowers.prepare lambda k).format.unit storedPrefix)
    (s : GeneralPaperQuantileStepPrice.Step) (rightWork : ℕ)
    (hLocal : s.left.work+rightWork+s.through.work+s.comparison.work+24≤GeneralPaperQuantileWork.stepPrice lambda k digits)
    (bit : Bool) :
    (finish primitive W bit (run bits primitive W c digits j total height node ancestor storedMass storedPrefix).1 s rightWork).2≤
      12*primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+128*W := by
  rw [GeneralPaperQuantileDescentData.data bits primitive W m lambda k Qv digits j c hc total height node ancestor
    storedMass storedPrefix hHeight hValid hPath hMass hPrefix]
  apply GeneralPaperQuantileDescentControls.return_work primitive hMono W m lambda k Qv height _ s rightWork hHeight
  · rw [hc,hDigits]
    exact GeneralPaperQuantileWork.run_work lambda k _ j _ total height node ancestor storedMass storedPrefix
  · exact GeneralPaperQuantileDescent.visits _ _ _ _ _ _ _ _ _ _
  · rw [hDigits] at hLocal
    exact hLocal

end Blotto.GeneralPaperQuantileDescentReturn
