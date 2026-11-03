import Blotto.GeneralPaperQuantileRecordStorage

/-! A conservative live-frame reservation for one native quantile descent.
All ancestor records and returned child paths are counted together. This
may count shared path tails repeatedly, and therefore gives a quadratic
depth bound. It does not expand virtual tree cursors or execute an observer.
Primitive arithmetic scratch is joined separately to the operation ledger. -/
namespace Blotto.GeneralPaperQuantileTraversalStorage
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperIntervalLevels
open GeneralPaperGlobalNodeQuery GeneralPaperMassApproximation
open GeneralPaperQuantileDescent GeneralPaperQuantileRecordStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def peak (W : ℕ) (p : GeneralPaperPreparedPowers.Prepared) (digits j s : ℕ) (total : Number) :
    (height : ℕ) → Node height → ℕ → Number → Number → ℕ
  | 0,node,ancestor,storedMass,storedPrefix =>
    inputBits W digits j ancestor node total storedMass storedPrefix+
      resultBits W (run p digits j s total 0 node ancestor storedMass storedPrefix)
  | height+1,node,ancestor,storedMass,storedPrefix =>
    let left := leftMass p ancestor node storedMass
    let right := rightMass p ancestor node storedMass
    let through := GeneralPaperDyadicAddition.add p.format.unit p.format.fractionalBits storedPrefix left.number
    let comp := GeneralPaperDyadicCompare.scaledLE digits j total s through.number
    inputBits W digits j ancestor node total storedMass storedPrefix+
      stepBits W left right through comp+
      resultBits W (run p digits j s total (height+1) node ancestor storedMass storedPrefix)+128*W+
      if comp.answer then
        peak W p digits j s total height (leftChild node) (ancestor+offset node) left.number storedPrefix
      else
        peak W p digits j s total height (rightChild node) (ancestor+offset node) right.number through.number

def coefficient (W m lambda k Qv : ℕ) : ℕ :=
  32*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+1024*W+4

theorem bounded (W m lambda k Qv digits j : ℕ) (total : Number)
    (height : ℕ) (node : Node height) (ancestor : ℕ) (storedMass storedPrefix : Number)
    (hd : digits=GeneralPaperQuantileComparison.width lambda k)
    (hj : j≤(GeneralPaperSourceParameters.prepare k).summarySize) (hh : height≤lambda+1)
    (hv : Valid lambda k node)
    (hp : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (hm : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
      (trueMass k ancestor node) storedMass)
    (ht : Normal (GeneralPaperPreparedPowers.prepare lambda k).format.unit total)
    (hpre : Normal (GeneralPaperPreparedPowers.prepare lambda k).format.unit storedPrefix)
    (hs : GeneralPaperQuantileExponentRange.Safe lambda k digits j (GeneralPaperSourceParameters.prepare k).summarySize
      total height node ancestor storedMass storedPrefix) :
    peak W (GeneralPaperPreparedPowers.prepare lambda k) digits j (GeneralPaperSourceParameters.prepare k).summarySize
      total height node ancestor storedMass storedPrefix≤(height+1)^2*coefficient W m lambda k Qv := by
  let p := GeneralPaperPreparedPowers.prepare lambda k
  let C := coefficient W m lambda k Qv
  have hC : 1+2*W≤C := by dsimp [C,coefficient]; omega
  induction height generalizing ancestor storedMass storedPrefix with
  | zero =>
    have hi := input_bound W m lambda k Qv digits j 0 ancestor node total storedMass storedPrefix
      hd hj hh hp ht hm.1 hpre hs
    have hr := result_bound W m lambda k Qv digits j (GeneralPaperSourceParameters.prepare k).summarySize
      0 ancestor total storedMass storedPrefix node hd hh
    rw [peak]
    norm_num only [Nat.zero_add,one_pow,one_mul]
    change inputBits W digits j ancestor node total storedMass storedPrefix+
      resultBits W (run p digits j (GeneralPaperSourceParameters.prepare k).summarySize total 0 node ancestor storedMass storedPrefix)≤C
    dsimp only [p,C,coefficient]
    omega
  | succ height ih =>
    let left := leftMass p ancestor node storedMass
    let right := rightMass p ancestor node storedMass
    let through := GeneralPaperDyadicAddition.add p.format.unit p.format.fractionalBits storedPrefix left.number
    let comp := GeneralPaperDyadicCompare.scaledLE digits j total (GeneralPaperSourceParameters.prepare k).summarySize through.number
    have hi := input_bound W m lambda k Qv digits j (height+1) ancestor node total storedMass storedPrefix
      hd hj hh hp ht hm.1 hpre hs.1
    have hr := result_bound W m lambda k Qv digits j (GeneralPaperSourceParameters.prepare k).summarySize
      (height+1) ancestor total storedMass storedPrefix node hd hh
    have hStep := step_bound W m lambda k Qv digits j ancestor node total storedMass storedPrefix hd hh hv hp hm hpre hs
    change stepBits W left right through comp≤_ at hStep
    have hProd := Nat.mul_le_mul_left (height+1) hC
    have hLocal : inputBits W digits j ancestor node total storedMass storedPrefix+
        stepBits W left right through comp+
        resultBits W (run p digits j (GeneralPaperSourceParameters.prepare k).summarySize total (height+1) node ancestor storedMass storedPrefix)+
        128*W≤(height+1)*C+C := by
      have hFixed : 17*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+1+704*W≤C := by
        dsimp [C,coefficient]; omega
      dsimp only [p]
      omega
    have hChildren := child_validity lambda k node hv
    have hPaths := child_paths _ ancestor node hp
    have hL := GeneralPaperQuantileChildMass.left_bound lambda k ancestor node storedMass hh hv hp hm
    have hR := GeneralPaperQuantileChildMass.right_bound lambda k ancestor node storedMass hh hv hp hm
    have hThrough : Normal p.format.unit through.number := GeneralPaperDyadicAddition.add_normal _ _
      (GeneralPaperPowerPrecision.unit_positive lambda k) (GeneralPaperPowerPrecision.unit_power lambda k) _ _ hpre hL.1
    have hNext := hs.2.2.2.2
    change (if comp.answer then _ else _) at hNext
    rw [peak]
    change inputBits W digits j ancestor node total storedMass storedPrefix+stepBits W left right through comp+
      resultBits W (run p digits j (GeneralPaperSourceParameters.prepare k).summarySize total (height+1) node ancestor storedMass storedPrefix)+128*W+
      (if comp.answer then _ else _)≤(height+1+1)^2*C
    split
    · rename_i hb
      simp only [hb,ite_true] at hNext
      have hc := ih (leftChild node) (ancestor+offset node) left.number storedPrefix (by omega)
        hChildren.1 hPaths.1 hL hpre hNext
      have hSum := Nat.add_le_add hLocal hc
      exact hSum.trans (by nlinarith only [Nat.zero_le ((height+1)*C)])
    · rename_i hb
      simp only [hb,ite_false,Bool.false_eq_true] at hNext
      have hc := ih (rightChild node) (ancestor+offset node) right.number through.number (by omega)
        hChildren.2 hPaths.2 hR hThrough hNext
      have hSum := Nat.add_le_add hLocal hc
      exact hSum.trans (by nlinarith only [Nat.zero_le ((height+1)*C)])

theorem root (W m lambda k Qv digits j height : ℕ) (node : Node height)
    (hd : digits=GeneralPaperQuantileComparison.width lambda k)
    (hj : j≤(GeneralPaperSourceParameters.prepare k).summarySize) (hh : height≤lambda+1)
    (hv : Valid lambda k node) (hp : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    let p := GeneralPaperPreparedPowers.prepare lambda k
    let total := (fresh p 0 node).number
    peak W p digits j (GeneralPaperSourceParameters.prepare k).summarySize total height node 0 total zero≤
      (height+1)^2*coefficient W m lambda k Qv := by
  dsimp only
  have hm := fresh_bound lambda k 0 node hh hv hp
  exact bounded W m lambda k Qv digits j _ height node 0 _ zero hd hj hh hv hp hm hm.1
    (zero_bound _ (queryExponent lambda k)).1 (GeneralPaperQuantileExponentRange.initial lambda k digits j _ height node hh hv hp)

end Blotto.GeneralPaperQuantileTraversalStorage
