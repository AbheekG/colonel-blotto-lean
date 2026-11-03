import Blotto.GeneralPaperQuantileDescentReturn

/-! Full bit-price bound along the actual selected path. All operand,
annotation, control and recursive-state premises are derived from the native
mass certificate, validity/path caps and the already-checked Safe invariant.
The caller reference word W remains explicit until the global capacity join.
-/
namespace Blotto.GeneralPaperQuantileDescentBits
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperIntervalLevels
open GeneralPaperMassApproximation GeneralPaperGlobalNodeQuery
open GeneralPaperQuantileDescentExecution GeneralPaperSourcePreparationSizes
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv digits j : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (total : Number)
    (height : ℕ) (node : Node height) (ancestor : ℕ) (storedMass storedPrefix : Number)
    (hJ : j≤(GeneralPaperSourceParameters.prepare k).summarySize) (hHeight : height≤lambda+1)
    (hValid : Valid lambda k node) (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (hMass : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
      (trueMass k ancestor node) storedMass)
    (hTotal : Normal (GeneralPaperPreparedPowers.prepare lambda k).format.unit total)
    (hPrefix : Normal (GeneralPaperPreparedPowers.prepare lambda k).format.unit storedPrefix)
    (hSafe : GeneralPaperQuantileExponentRange.Safe lambda k digits j (GeneralPaperSourceParameters.prepare k).summarySize
      total height node ancestor storedMass storedPrefix) :
    (run true primitive W c digits j total height node ancestor storedMass storedPrefix).2≤
      8388608*(height+1)*(measure m lambda k Qv+1)*
        (W+primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := by
  subst c
  subst digits
  let c := GeneralPaperMaterializedPowerCache.specification m lambda k Qv
  let digits := GeneralPaperQuantileComparison.width lambda k
  let M := measure m lambda k Qv
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let B := W+primitive H
  change (run true primitive W c digits j total height node ancestor storedMass storedPrefix).2≤8388608*(height+1)*(M+1)*B
  induction height generalizing ancestor storedMass storedPrefix with
  | zero =>
    have hWord : 1+binaryWordWidth 0≤H := by
      have hm := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
      have hz : binaryWordWidth 0=1 := by decide
      dsimp [H,GeneralPaperPowerPreparationEnvelope.operandWidth]; omega
    have ht := GeneralPaperIntegerWordPrice.compare_le primitive hMono 0 0 H hWord hWord
    change 64*W+GeneralPaperIntegerWordPrice.compare primitive 0 0≤8388608*(0+1)*(M+1)*B
    dsimp only [B]
    nlinarith only [ht,Nat.zero_le M]
  | succ height ih =>
    let ns := GeneralPaperQuantileStepPrice.specification c digits j ancestor node total storedMass storedPrefix
    let nr := GeneralPaperQuantileDescent.rightMass c.powers ancestor node storedMass
    have hChildren := child_validity lambda k node hValid
    have hPaths := child_paths _ ancestor node hPath
    have hL := GeneralPaperQuantileChildMass.left_bound lambda k ancestor node storedMass hHeight hValid hPath hMass
    have hR := GeneralPaperQuantileChildMass.right_bound lambda k ancestor node storedMass hHeight hValid hPath hMass
    have hLN : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
        (trueMass k (ancestor+offset node) (leftChild node)) ns.left.number := hL
    have hRN : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit (queryExponent lambda k)
        (trueMass k (ancestor+offset node) (rightChild node)) nr.number := hR
    have hThrough : Normal (GeneralPaperPreparedPowers.prepare lambda k).format.unit ns.through.number :=
      GeneralPaperDyadicAddition.add_normal _ _ (GeneralPaperPowerPrecision.unit_positive lambda k)
        (GeneralPaperPowerPrecision.unit_power lambda k) _ _ hPrefix hL.1
    have hp : Normal c.powers.format.unit storedPrefix := hPrefix
    have hSD := GeneralPaperQuantileDescentData.step_data true primitive W m lambda k Qv digits j ancestor c rfl
      node total storedMass storedPrefix hHeight hValid hPath hMass hp
    change (step true primitive W c digits j ancestor node total storedMass storedPrefix).1=ns at hSD
    have hRD := GeneralPaperQuantileDescentData.right_data true primitive W m lambda k Qv ancestor c rfl node storedMass hValid hPath
    change (right true primitive W c ancestor node storedMass).1=nr at hRD
    have hStep := GeneralPaperQuantileStepPrice.work primitive hMono W m lambda k Qv digits j ancestor c rfl rfl
      node total storedMass storedPrefix hJ hHeight hValid hPath hMass hTotal hPrefix hSafe
    change (step true primitive W c digits j ancestor node total storedMass storedPrefix).2≤4194304*(M+1)*B at hStep
    have hAdvance := GeneralPaperQuantileDescentControls.advance_work primitive hMono W m lambda k Qv height ancestor (offset node)
      hHeight (path_offset _ ancestor node hPath)
    change advance primitive W height ancestor (offset node)≤6*primitive H+128*W at hAdvance
    have hLocal := GeneralPaperQuantileDescentReturn.local_work lambda k digits j
      (GeneralPaperSourceParameters.prepare k).summarySize ancestor node total storedMass storedPrefix
    change ns.left.work+nr.work+ns.through.work+ns.comparison.work+24≤GeneralPaperQuantileWork.stepPrice lambda k digits at hLocal
    have hLocalLeft : ns.left.work+0+ns.through.work+ns.comparison.work+24≤GeneralPaperQuantileWork.stepPrice lambda k digits := by omega
    change GeneralPaperQuantileExponentRange.StateBound _ _ _ _ ∧ _ ∧ _ ∧ _ ∧
      (if ns.comparison.answer then
        GeneralPaperQuantileExponentRange.Safe lambda k digits j (GeneralPaperSourceParameters.prepare k).summarySize total height
          (leftChild node) (ancestor+offset node) ns.left.number storedPrefix
       else GeneralPaperQuantileExponentRange.Safe lambda k digits j (GeneralPaperSourceParameters.prepare k).summarySize total height
          (rightChild node) (ancestor+offset node) nr.number ns.through.number) at hSafe
    rw [run]
    dsimp only
    rw [hSD]
    split
    · rename_i hBranch
      have hNext := hSafe.2.2.2.2
      simp only [hBranch,ite_true] at hNext
      have hi := ih (leftChild node) (ancestor+offset node) ns.left.number storedPrefix (by omega)
        hChildren.1 hPaths.1 hLN hPrefix hNext
      have hf := GeneralPaperQuantileDescentReturn.work true primitive hMono W m lambda k Qv digits j c rfl rfl total
        height (leftChild node) (ancestor+offset node) ns.left.number storedPrefix (by omega) hChildren.1 hPaths.1 hLN hPrefix ns 0 hLocalLeft false
      change _≤12*primitive H+128*W at hf
      change (step true primitive W c digits j ancestor node total storedMass storedPrefix).2+
        advance primitive W height ancestor (offset node)+
        (run true primitive W c digits j total height (leftChild node) (ancestor+offset node) ns.left.number storedPrefix).2+
        (finish primitive W false
          (run true primitive W c digits j total height (leftChild node) (ancestor+offset node) ns.left.number storedPrefix).1 ns 0).2≤
          8388608*(height+1+1)*(M+1)*B
      dsimp only [B] at hStep hi ⊢
      nlinarith only [hStep,hAdvance,hi,hf,Nat.zero_le M]
    · rename_i hBranch
      have hNext := hSafe.2.2.2.2
      simp only [hBranch,ite_false,Bool.false_eq_true] at hNext
      have hi := ih (rightChild node) (ancestor+offset node) nr.number ns.through.number (by omega)
        hChildren.2 hPaths.2 hRN hThrough hNext
      have hf := GeneralPaperQuantileDescentReturn.work true primitive hMono W m lambda k Qv digits j c rfl rfl total
        height (rightChild node) (ancestor+offset node) nr.number ns.through.number (by omega) hChildren.2 hPaths.2 hRN hThrough ns nr.work hLocal true
      change _≤12*primitive H+128*W at hf
      have hr := GeneralPaperChildMassStatePrice.work true primitive hMono W m lambda k Qv c rfl ancestor node storedMass
        hHeight hValid hPath hMass
      change (right true primitive W c ancestor node storedMass).2≤1048576*(M+1)*B at hr
      rw [hRD]
      change (step true primitive W c digits j ancestor node total storedMass storedPrefix).2+
        advance primitive W height ancestor (offset node)+(right true primitive W c ancestor node storedMass).2+
        (run true primitive W c digits j total height (rightChild node) (ancestor+offset node) nr.number ns.through.number).2+
        (finish primitive W true
          (run true primitive W c digits j total height (rightChild node) (ancestor+offset node) nr.number ns.through.number).1 ns nr.work).2≤
          8388608*(height+1+1)*(M+1)*B
      dsimp only [B] at hStep hi hr ⊢
      nlinarith only [hStep,hAdvance,hi,hf,hr,Nat.zero_le M]

end Blotto.GeneralPaperQuantileDescentBits
