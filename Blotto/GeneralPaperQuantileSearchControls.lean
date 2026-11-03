import Blotto.GeneralPaperQuantileSearchExecution

/-! Root return metadata is bounded from native fresh/descent annotations.
Its encoded word is at most four times the retained operand word. These
capacities are erased proof quantities, not supplied execution inputs.
-/
namespace Blotto.GeneralPaperQuantileSearchControls
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery GeneralPaperSourcePreparationSizes
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def cap (m lambda k Qv : ℕ) : ℕ := 2*GeneralPaperQuantileDescentControls.cap m lambda k Qv+8*(lambda+2)+1024

theorem cap_word (m lambda k Qv : ℕ) :
    1+binaryWordWidth (cap m lambda k Qv)≤4*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  have hC := GeneralPaperQuantileDescentControls.cap_word m lambda k Qv
  have hL := GeneralPaperQuantileDescentControls.height_word m lambda k Qv
  change _≤H at hC hL
  have ha := binaryWordWidth_mul 2 (GeneralPaperQuantileDescentControls.cap m lambda k Qv)
  have hb := binaryWordWidth_mul 8 (lambda+2)
  have hc := GeneralPaperRayOperandWidthEnvelope.word_add (2*GeneralPaperQuantileDescentControls.cap m lambda k Qv) (8*(lambda+2))
  have hd := GeneralPaperRayOperandWidthEnvelope.word_add (2*GeneralPaperQuantileDescentControls.cap m lambda k Qv+8*(lambda+2)) 1024
  have h2 : binaryWordWidth 2=2 := by decide
  have h8 : binaryWordWidth 8=4 := by decide
  have h1024 : binaryWordWidth 1024=11 := by decide
  have hm := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  have hH : 64≤H := by dsimp [H,GeneralPaperPowerPreparationEnvelope.operandWidth]; omega
  change 1+binaryWordWidth (2*GeneralPaperQuantileDescentControls.cap m lambda k Qv+8*(lambda+2)+1024)≤4*H
  omega

theorem metadata_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (t d height N L : ℕ)
    (hSum : t+d+8*height+16≤N) (hHeight : height≤N) (hWord : 1+binaryWordWidth N≤L) :
    GeneralPaperQuantileSearchExecution.metadata primitive t d height≤8*primitive L := by
  have price (op : ℕ → ℕ → ℕ) (a b : ℕ) (ha : a≤N) (hb : b≤N) (hc : op a b≤N) :
      GeneralPaperNaturalPrimitivePrice.binary primitive op a b≤2*primitive L :=
    (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono op a b N ha hb hc).trans
      (Nat.mul_le_mul_left 2 (hMono hWord))
  have a := price (fun a b => a*b) 8 height (by omega) hHeight (by omega)
  have b := price (fun a b => a+b) t d (by omega) (by omega) (by omega)
  have c := price (fun a b => a+b) (t+d) (8*height) (by omega) (by omega) (by omega)
  have d := price (fun a b => a+b) (t+d+8*height) 16 (by omega) (by omega) hSum
  unfold GeneralPaperQuantileSearchExecution.metadata
  omega

theorem native_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (m lambda k Qv digits j height : ℕ)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (node : Node height) (hHeight : height≤lambda+1) :
    let p := GeneralPaperPreparedPowers.prepare lambda k
    let t := fresh p 0 node
    let d := GeneralPaperQuantileDescent.run p digits j (GeneralPaperSourceParameters.prepare k).summarySize t.number height node 0 t.number zero
    GeneralPaperQuantileSearchExecution.metadata primitive t.work d.work height≤
      8*primitive (4*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) := by
  let A := 1048576*(measure m lambda k Qv+1)^2
  have hp := GeneralPaperQuantileDescentControls.step_price m lambda k Qv
  rw [←hDigits] at hp
  change GeneralPaperQuantileWork.stepPrice lambda k digits≤A at hp
  have hm := fresh_work lambda k 0 node
  change (fresh (GeneralPaperPreparedPowers.prepare lambda k) 0 node).work≤GeneralPaperQuantileWork.massPrice lambda k at hm
  have hMass : GeneralPaperQuantileWork.massPrice lambda k≤GeneralPaperQuantileWork.stepPrice lambda k digits := by
    unfold GeneralPaperQuantileWork.stepPrice; omega
  have ht := hm.trans (hMass.trans hp)
  have hd := GeneralPaperQuantileWork.run_work lambda k digits j (GeneralPaperSourceParameters.prepare k).summarySize
    (fresh (GeneralPaperPreparedPowers.prepare lambda k) 0 node).number height node 0
    (fresh (GeneralPaperPreparedPowers.prepare lambda k) 0 node).number zero
  have hD := hd.trans (Nat.add_le_add_right (Nat.mul_le_mul_left height hp) 8)
  have hProduct := Nat.mul_le_mul_right A hHeight
  apply metadata_work primitive hMono _ _ height (cap m lambda k Qv) _ _ _ (cap_word m lambda k Qv)
  · change _≤2*((lambda+2)*A+256)+8*(lambda+2)+1024
    nlinarith only [ht,hD,hProduct,hHeight]
  · change height≤2*((lambda+2)*A+256)+8*(lambda+2)+1024
    omega

end Blotto.GeneralPaperQuantileSearchControls
