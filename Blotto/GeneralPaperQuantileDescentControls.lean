import Blotto.GeneralPaperQuantileDescentData

/-! Native annotations and cursor controls have derived encoded widths.
The cap is analytical and no integer representation is decoded at runtime.
It bounds every addition used to return a step and every visit increment.
-/
namespace Blotto.GeneralPaperQuantileDescentControls
open GeneralPaperQuantileDescentExecution GeneralPaperSourcePreparationSizes
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def cap (m lambda k Qv : ℕ) : ℕ := (lambda+2)*(1048576*(measure m lambda k Qv+1)^2)+256

theorem step_price (m lambda k Qv : ℕ) :
    GeneralPaperQuantileWork.stepPrice lambda k (GeneralPaperQuantileComparison.width lambda k)≤
      1048576*(measure m lambda k Qv+1)^2 := by
  let M := measure m lambda k Qv
  let f := GeneralPaperPowerPrecision.prepare lambda k
  have hp := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).fractionalBits
  have hc := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).columns
  have hd := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).comparison
  change f.fractionalBits≤128*M at hp
  change f.columns≤32*M at hc
  change GeneralPaperQuantileComparison.width lambda k≤256*M at hd
  have hMul := Nat.mul_le_mul hc (show 12*(f.fractionalBits+1)+82≤1536*M+94 by omega)
  have hMass : GeneralPaperQuantileWork.massPrice lambda k≤262144*(M+1)^2 := by
    change f.columns*(12*(f.fractionalBits+1)+82)+12*(f.fractionalBits+1)+92≤_
    nlinarith only [hMul,hp,Nat.zero_le M]
  change 2*GeneralPaperQuantileWork.massPrice lambda k+8*f.fractionalBits+
    12*(f.fractionalBits+1)+8*GeneralPaperQuantileComparison.width lambda k+150≤1048576*(M+1)^2
  nlinarith only [hMass,hp,hd,Nat.zero_le M]

theorem height_word (m lambda k Qv : ℕ) :
    1+binaryWordWidth (lambda+2)≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have hh : binaryWordWidth (lambda+1)≤measure m lambda k Qv := by unfold GeneralPaperSourcePreparationSizes.measure; omega
  have hAdd := GeneralPaperRayOperandWidthEnvelope.word_add (lambda+1) 1
  have hLambda : lambda+1+1=lambda+2 := by omega
  rw [hLambda] at hAdd
  have h1 : binaryWordWidth 1=1 := by decide
  have hm := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  unfold GeneralPaperPowerPreparationEnvelope.operandWidth
  omega

theorem cap_word (m lambda k Qv : ℕ) :
    1+binaryWordWidth (cap m lambda k Qv)≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  let M := measure m lambda k Qv
  have hh : binaryWordWidth (lambda+1)≤M := by dsimp [M,GeneralPaperSourcePreparationSizes.measure]; omega
  have hAdd := GeneralPaperRayOperandWidthEnvelope.word_add (lambda+1) 1
  have hLambda : lambda+1+1=lambda+2 := by omega
  rw [hLambda] at hAdd
  have hMWord := GeneralPaperInitializerControlCounters.word_le_self (M+1)
  have hSq := binaryWordWidth_mul (M+1) (M+1)
  have hPow := binaryWordWidth_mul 1048576 ((M+1)^2)
  have hTop := binaryWordWidth_mul (lambda+2) (1048576*(M+1)^2)
  have hLast := GeneralPaperRayOperandWidthEnvelope.word_add ((lambda+2)*(1048576*(M+1)^2)) 256
  have h1 : binaryWordWidth 1=1 := by decide
  have hBig : binaryWordWidth 1048576=21 := by decide
  have h256 : binaryWordWidth 256=9 := by decide
  have hm := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  rw [←pow_two] at hSq
  change 1+binaryWordWidth ((lambda+2)*(1048576*(M+1)^2)+256)≤1048576*M
  change 128≤M at hm
  omega

theorem metadata_work (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (child : GeneralPaperQuantileDescent.Result) (s : GeneralPaperQuantileStepPrice.Step) (rightWork N L : ℕ)
    (hSum : child.work+s.left.work+rightWork+s.through.work+s.comparison.work+24≤N)
    (hVisits : child.visits+1≤N) (hWord : 1+binaryWordWidth N≤L) :
    metadata primitive child s rightWork≤12*primitive L := by
  have price (a b : ℕ) (ha : a≤N) (hb : b≤N) (hc : a+b≤N) :
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) a b≤2*primitive L :=
    (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a+b) a b N ha hb hc).trans
      (Nat.mul_le_mul_left 2 (hMono hWord))
  have a := price child.work s.left.work (by omega) (by omega) (by omega)
  have b := price (child.work+s.left.work) rightWork (by omega) (by omega) (by omega)
  have c := price (child.work+s.left.work+rightWork) s.through.work (by omega) (by omega) (by omega)
  have d := price (child.work+s.left.work+rightWork+s.through.work) s.comparison.work (by omega) (by omega) (by omega)
  have e := price (child.work+s.left.work+rightWork+s.through.work+s.comparison.work) 24 (by omega) (by omega) hSum
  have f := price child.visits 1 (by omega) (by omega) hVisits
  unfold metadata
  omega

theorem advance_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv height ancestor level : ℕ)
    (hHeight : height+1≤lambda+1) (hLevel : ancestor+level≤GeneralPaperPowerPrecision.levelBound lambda k) :
    advance primitive W height ancestor level≤6*primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+128*W := by
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let G := GeneralPaperPowerPrecision.levelBound lambda k
  have hHW := height_word m lambda k Qv
  have hGW := GeneralPaperFreshMassPrice.offset_width m lambda k Qv
  have hA := (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a+b) ancestor level G
    (by dsimp [G]; omega) (by dsimp [G]; omega) hLevel).trans (Nat.mul_le_mul_left 2 (hMono hGW))
  have hD := (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a-b) (height+1) 1 (lambda+2)
    (by omega) (by omega) (by omega)).trans (Nat.mul_le_mul_left 2 (hMono hHW))
  have hT := GeneralPaperIntegerWordPrice.compare_le primitive hMono (height+1) 0 H
    ((Nat.add_le_add_left (binaryWordWidth_mono (by omega : height+1≤lambda+2)) 1).trans hHW)
    ((Nat.add_le_add_left (binaryWordWidth_mono (Nat.zero_le (lambda+2))) 1).trans hHW)
  have hW := hMono ((Nat.add_le_add_left (binaryWordWidth_mono (by omega : height≤lambda+2)) 1).trans hHW)
  change _≤2*primitive H at hA hD
  change _≤primitive H at hW
  change _≤6*primitive H+128*W
  unfold advance
  omega

theorem return_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv height : ℕ)
    (child : GeneralPaperQuantileDescent.Result) (s : GeneralPaperQuantileStepPrice.Step) (rightWork : ℕ)
    (hHeight : height≤lambda+1)
    (hChild : child.work≤height*GeneralPaperQuantileWork.stepPrice lambda k (GeneralPaperQuantileComparison.width lambda k)+8)
    (hVisits : child.visits=height+1)
    (hLocal : s.left.work+rightWork+s.through.work+s.comparison.work+24≤
      GeneralPaperQuantileWork.stepPrice lambda k (GeneralPaperQuantileComparison.width lambda k)) (bit : Bool) :
    (finish primitive W bit child s rightWork).2≤
      12*primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+128*W := by
  let A := 1048576*(measure m lambda k Qv+1)^2
  have hA : 1≤A := by dsimp [A]; nlinarith only [Nat.zero_le (measure m lambda k Qv)]
  have hp := step_price m lambda k Qv
  change _≤A at hp
  have hP : height*GeneralPaperQuantileWork.stepPrice lambda k (GeneralPaperQuantileComparison.width lambda k)≤height*A :=
    Nat.mul_le_mul_left height hp
  have hH : height*A≤(lambda+1)*A := Nat.mul_le_mul_right A hHeight
  have hSum : child.work+s.left.work+rightWork+s.through.work+s.comparison.work+24≤cap m lambda k Qv := by
    change _≤(lambda+2)*A+256
    nlinarith only [hChild,hLocal,hp,hP,hH]
  have hv : child.visits+1≤cap m lambda k Qv := by
    rw [hVisits]
    change _≤(lambda+2)*A+256
    nlinarith only [hHeight,hA]
  exact Nat.add_le_add_right (metadata_work primitive hMono child s rightWork _ _ hSum hv (cap_word m lambda k Qv)) _

end Blotto.GeneralPaperQuantileDescentControls
