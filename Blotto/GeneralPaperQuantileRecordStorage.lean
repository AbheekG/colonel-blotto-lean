import Blotto.GeneralPaperSummaryArrayControls
import Blotto.GeneralPaperStoredNumberBits
import Blotto.GeneralPaperSparseNodeBits

/-! Encodings of the actual quantile input, returned path and native step
records. Work fields are stored data, distinct from erased operation prices.
Floating values keep their literal mantissa and signed exponent. -/
namespace Blotto.GeneralPaperQuantileRecordStorage
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperIntervalLevels
open GeneralPaperGlobalNodeQuery GeneralPaperMassApproximation
open GeneralPaperQuantileDescent GeneralPaperSourcePreparationSizes
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def resultBits (W : ℕ) (r : Result) : ℕ :=
  r.path.length*(1+2*W)+(1+binaryWordWidth r.work)+(1+binaryWordWidth r.visits)+64*W

def inputBits {height : ℕ} (W digits j ancestor : ℕ) (node : Node height)
    (total storedMass storedPrefix : Number) : ℕ :=
  GeneralPaperStoredNumberBits.bits total+GeneralPaperStoredNumberBits.bits storedMass+
    GeneralPaperStoredNumberBits.bits storedPrefix+
    (1+binaryWordWidth digits)+(1+binaryWordWidth j)+(1+binaryWordWidth ancestor)+
    (1+binaryWordWidth (offset node))+(1+binaryWordWidth height)+256*W

def stepBits (W : ℕ) (left right through : GeneralPaperDyadicMultiply.Result)
    (comparison : GeneralPaperDyadicCompare.Result) : ℕ :=
  GeneralPaperStoredNumberBits.bits left.number+GeneralPaperStoredNumberBits.bits right.number+
    GeneralPaperStoredNumberBits.bits through.number+
    (1+binaryWordWidth left.work)+(1+binaryWordWidth right.work)+
    (1+binaryWordWidth through.work)+(1+binaryWordWidth comparison.work)+1+256*W

theorem result_bound (W m lambda k Qv digits j s height ancestor : ℕ)
    (total storedMass storedPrefix : Number) (node : Node height)
    (hd : digits=GeneralPaperQuantileComparison.width lambda k) (hh : height≤lambda+1) :
    resultBits W (run (GeneralPaperPreparedPowers.prepare lambda k) digits j s total height node ancestor storedMass storedPrefix)≤
      height*(1+2*W)+2*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+64*W := by
  have hw := GeneralPaperQuantileWork.run_work lambda k digits j s total height node ancestor storedMass storedPrefix
  have hv := visits (GeneralPaperPreparedPowers.prepare lambda k) digits j s total height node ancestor storedMass storedPrefix
  have hp := GeneralPaperQuantileDescentControls.step_price m lambda k Qv
  rw [←hd] at hp
  have hprod := Nat.mul_le_mul hh hp
  have hcap : (run (GeneralPaperPreparedPowers.prepare lambda k) digits j s total height node ancestor storedMass storedPrefix).work≤
      GeneralPaperQuantileDescentControls.cap m lambda k Qv := by
    unfold GeneralPaperQuantileDescentControls.cap
    nlinarith only [hw,hprod,Nat.zero_le (1048576*(measure m lambda k Qv+1)^2)]
  have hww := binaryWordWidth_mono hcap
  have hcw := GeneralPaperQuantileDescentControls.cap_word m lambda k Qv
  have hvw := binaryWordWidth_mono (show height+1≤lambda+2 by omega)
  have hhw := GeneralPaperQuantileDescentControls.height_word m lambda k Qv
  unfold resultBits
  rw [path_length,hv]
  omega

theorem input_bound (W m lambda k Qv digits j height ancestor : ℕ) (node : Node height)
    (total storedMass storedPrefix : Number)
    (hd : digits=GeneralPaperQuantileComparison.width lambda k)
    (hj : j≤(GeneralPaperSourceParameters.prepare k).summarySize) (hh : height≤lambda+1)
    (hp : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (ht : Normal (GeneralPaperPreparedPowers.prepare lambda k).format.unit total)
    (hm : Normal (GeneralPaperPreparedPowers.prepare lambda k).format.unit storedMass)
    (hpre : Normal (GeneralPaperPreparedPowers.prepare lambda k).format.unit storedPrefix)
    (hb : GeneralPaperQuantileExponentRange.StateBound (GeneralPaperQuantileExponentRange.cap lambda k)
      total storedMass storedPrefix) :
    inputBits W digits j ancestor node total storedMass storedPrefix≤
      8*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+256*W := by
  have htW := GeneralPaperStoredNumberBits.operand m lambda k Qv total ht hb.1
  have hmW := GeneralPaperStoredNumberBits.operand m lambda k Qv storedMass hm hb.2.1
  have hpW := GeneralPaperStoredNumberBits.operand m lambda k Qv storedPrefix hpre hb.2.2
  have hhW := GeneralPaperSparseNodeBits.height_word m lambda k Qv height hh
  have hJ := (Nat.add_le_add_left (binaryWordWidth_mono hj) 1).trans
    (GeneralPaperSummaryArrayControls.size_word m lambda k Qv)
  have ho := path_offset _ ancestor node hp
  have haW := (Nat.add_le_add_left (binaryWordWidth_mono (show ancestor≤GeneralPaperPowerPrecision.levelBound lambda k by omega)) 1).trans
    (GeneralPaperFreshMassPrice.offset_width m lambda k Qv)
  have hlW := (Nat.add_le_add_left (binaryWordWidth_mono (show offset node≤GeneralPaperPowerPrecision.levelBound lambda k by omega)) 1).trans
    (GeneralPaperFreshMassPrice.offset_width m lambda k Qv)
  have hdW : 1+binaryWordWidth digits≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    have hdB := GeneralPaperQuantileComparisonPrice.digits_bound m lambda k Qv
    have hw := GeneralPaperInitializerControlCounters.word_le_self (digits+1)
    have hmono := binaryWordWidth_mono (Nat.le_add_right digits 1)
    have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
    rw [←hd] at hdB
    unfold GeneralPaperPowerPreparationEnvelope.operandWidth
    omega
  unfold inputBits
  omega

theorem step_bound (W m lambda k Qv digits j ancestor : ℕ) {height : ℕ}
    (node : Node (height+1)) (total storedMass storedPrefix : Number)
    (hd : digits=GeneralPaperQuantileComparison.width lambda k) (hh : height+1≤lambda+1)
    (hv : Valid lambda k node)
    (hp : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (hm : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
      (trueMass k ancestor node) storedMass)
    (hpre : Normal (GeneralPaperPreparedPowers.prepare lambda k).format.unit storedPrefix)
    (hs : GeneralPaperQuantileExponentRange.Safe lambda k digits j (GeneralPaperSourceParameters.prepare k).summarySize
      total (height+1) node ancestor storedMass storedPrefix) :
    let p := GeneralPaperPreparedPowers.prepare lambda k
    let left := leftMass p ancestor node storedMass
    let right := rightMass p ancestor node storedMass
    let through := GeneralPaperDyadicAddition.add p.format.unit p.format.fractionalBits storedPrefix left.number
    stepBits W left right through
      (GeneralPaperDyadicCompare.scaledLE digits j total (GeneralPaperSourceParameters.prepare k).summarySize through.number)≤
        7*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+1+256*W := by
  let p := GeneralPaperPreparedPowers.prepare lambda k
  let left := leftMass p ancestor node storedMass
  let right := rightMass p ancestor node storedMass
  let through := GeneralPaperDyadicAddition.add p.format.unit p.format.fractionalBits storedPrefix left.number
  let comp := GeneralPaperDyadicCompare.scaledLE digits j total (GeneralPaperSourceParameters.prepare k).summarySize through.number
  have hL := GeneralPaperQuantileChildMass.left_bound lambda k ancestor node storedMass hh hv hp hm
  have hR := GeneralPaperQuantileChildMass.right_bound lambda k ancestor node storedMass hh hv hp hm
  have hThrough : Normal p.format.unit through.number := GeneralPaperDyadicAddition.add_normal _ _
    (GeneralPaperPowerPrecision.unit_positive lambda k) (GeneralPaperPowerPrecision.unit_power lambda k) _ _ hpre hL.1
  have hlW := GeneralPaperStoredNumberBits.operand m lambda k Qv left.number hL.1 hs.2.1
  have hrW := GeneralPaperStoredNumberBits.operand m lambda k Qv right.number hR.1 hs.2.2.1
  have htW := GeneralPaperStoredNumberBits.operand m lambda k Qv through.number hThrough hs.2.2.2.1
  have hlocal := GeneralPaperQuantileDescentReturn.local_work lambda k digits j
    (GeneralPaperSourceParameters.prepare k).summarySize ancestor node total storedMass storedPrefix
  change left.work+right.work+through.work+comp.work+24≤GeneralPaperQuantileWork.stepPrice lambda k digits at hlocal
  have hprice := GeneralPaperQuantileDescentControls.step_price m lambda k Qv
  rw [←hd] at hprice
  have hcap : left.work+right.work+through.work+comp.work≤GeneralPaperQuantileDescentControls.cap m lambda k Qv := by
    unfold GeneralPaperQuantileDescentControls.cap
    nlinarith only [hlocal,hprice,Nat.zero_le ((lambda+1)*(1048576*(measure m lambda k Qv+1)^2))]
  have hw := GeneralPaperQuantileDescentControls.cap_word m lambda k Qv
  have a := binaryWordWidth_mono (show left.work≤GeneralPaperQuantileDescentControls.cap m lambda k Qv by omega)
  have b := binaryWordWidth_mono (show right.work≤GeneralPaperQuantileDescentControls.cap m lambda k Qv by omega)
  have c := binaryWordWidth_mono (show through.work≤GeneralPaperQuantileDescentControls.cap m lambda k Qv by omega)
  have d := binaryWordWidth_mono (show comp.work≤GeneralPaperQuantileDescentControls.cap m lambda k Qv by omega)
  change stepBits W left right through comp≤_
  unfold stepBits
  omega

end Blotto.GeneralPaperQuantileRecordStorage
