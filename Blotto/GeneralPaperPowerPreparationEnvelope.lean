import Blotto.GeneralPaperCachedPowerPreparation

/-! Constructed-input envelope for the full cached power materialization.
M is the previous parameter measure. All raw base/table/wrapper widths are
O(M); the arithmetic implementation costs O(M^2), the bit implementation
O(M*(W+Rat(O(M)))). This is a phase price, not the global space join.
-/
namespace Blotto.GeneralPaperPowerPreparationEnvelope
open GeneralPaperSourcePreparationSizes GeneralPaperScoreScaleParameters
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def operandWidth (m lambda k Qv : ℕ) : ℕ := 1048576*measure m lambda k Qv

structure Sizes (m lambda k Qv : ℕ) : Prop where
  baseChild : let f := GeneralPaperPowerPrecision.prepare lambda k
    8+2*(f.fractionalBits+1-GeneralPaperStoredGeometricBase.decrementBits k)≤operandWidth m lambda k Qv
  baseRaw : let f := GeneralPaperPowerPrecision.prepare lambda k
    GeneralPaperStoredBasePrice.rawWidth f.unit f.fractionalBits k
      (powerRun (f.fractionalBits+1-GeneralPaperStoredGeometricBase.decrementBits k))≤operandWidth m lambda k Qv
  table : let f := GeneralPaperPowerPrecision.prepare lambda k
    let b := GeneralPaperStoredGeometricBase.construct f.unit f.fractionalBits k
    GeneralPaperPowerTableBounds.width f.fractionalBits f.columns b.number≤operandWidth m lambda k Qv
  wrapper : let f := GeneralPaperPowerPrecision.prepare lambda k
    let b := GeneralPaperStoredGeometricBase.construct f.unit f.fractionalBits k
    let t := GeneralPaperRoundedPowerTable.build f.unit f.fractionalBits b.number f.columns
    GeneralPaperCachedPowerPreparation.wrapWidth f.work b.work t.work≤operandWidth m lambda k Qv

theorem sizes (m lambda k Qv : ℕ) : Sizes m lambda k Qv := by
  let M := measure m lambda k Qv
  let H := operandWidth m lambda k Qv
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let b := GeneralPaperStoredGeometricBase.construct f.unit f.fractionalBits k
  let t := GeneralPaperRoundedPowerTable.build f.unit f.fractionalBits b.number f.columns
  let e := f.fractionalBits+1-GeneralPaperStoredGeometricBase.decrementBits k
  let q := powerRun e
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).1
  change k+128≤M at hM
  have hm := GeneralPaperSourcePreparationControls.metadata m lambda k Qv
  have hp := hm.fractionalBits
  have hc := hm.columns
  have hf := hm.precisionWork
  change f.fractionalBits≤128*M at hp
  change f.columns≤32*M at hc
  change f.work≤8192*M at hf
  have he : e≤f.fractionalBits+1 := by dsimp only [e]; omega
  have hu := GeneralPaperParameterOperandBounds.dyadic_word f.fractionalBits
  rw [(power_data f.fractionalBits).1,←GeneralPaperPowerPrecision.unit_power lambda k] at hu
  change binaryWordWidth f.unit≤1+2*f.fractionalBits at hu
  have hq := GeneralPaperStoredGeometricBase.quantum_bound f.unit f.fractionalBits k (GeneralPaperPowerPrecision.unit_power lambda k)
  change q.power≤f.unit at hq
  have hqw := binaryWordWidth_mono hq
  have hqp := (power_data e).2.2
  change q.work=8*e+2 at hqp
  have hwq := GeneralPaperInitializerControlCounters.word_le_self q.work
  have hwp := GeneralPaperInitializerControlCounters.word_le_self f.fractionalBits
  have hwk := GeneralPaperInitializerControlCounters.word_le_self k
  have hfw := GeneralPaperInitializerControlCounters.word_le_self f.work
  have hBase := GeneralPaperStoredGeometricBase.construct_work f.unit f.fractionalBits k
  change b.work=8*e+18 at hBase
  have hbw := GeneralPaperInitializerControlCounters.word_le_self b.work
  have hbe : b.number.exponent.natAbs=f.fractionalBits+1 := by
    simp only [b,GeneralPaperStoredGeometricBase.construct,Int.natAbs_neg,Int.natAbs_natCast]
  have hBWord : binaryWordWidth (b.number.exponent.natAbs+f.fractionalBits+1)≤f.fractionalBits+4 := by
    rw [hbe,show f.fractionalBits+1+f.fractionalBits+1=2*(f.fractionalBits+1) by omega]
    have hh := binaryWordWidth_mul 2 (f.fractionalBits+1)
    have hs := GeneralPaperInitializerControlCounters.word_le_self (f.fractionalBits+1)
    have h2 : binaryWordWidth 2=2 := by decide
    omega
  have ht := GeneralPaperRoundedPowerTable.build_work f.unit f.fractionalBits f.columns b.number
  change t.work≤f.columns*(12*(f.fractionalBits+1)+82)+2 at ht
  have htw := binaryWordWidth_mono ht
  have hCols := GeneralPaperInitializerControlCounters.word_le_self f.columns
  have hA := GeneralPaperInitializerControlCounters.word_le_self (12*(f.fractionalBits+1)+82)
  have hProd := binaryWordWidth_mul f.columns (12*(f.fractionalBits+1)+82)
  have hSum := GeneralPaperRayOperandWidthEnvelope.word_add (f.columns*(12*(f.fractionalBits+1)+82)) 2
  have h2 : binaryWordWidth 2=2 := by decide
  have hChild : 8+2*e≤H := by dsimp [H,operandWidth]; omega
  have hRaw : GeneralPaperStoredBasePrice.rawWidth f.unit f.fractionalBits k q≤H := by
    dsimp [GeneralPaperStoredBasePrice.rawWidth,H,operandWidth]
    omega
  have hTable : GeneralPaperPowerTableBounds.width f.fractionalBits f.columns b.number≤H := by
    dsimp [GeneralPaperPowerTableBounds.width,H,operandWidth]
    omega
  have hWrapper : GeneralPaperCachedPowerPreparation.wrapWidth f.work b.work t.work≤H := by
    dsimp [GeneralPaperCachedPowerPreparation.wrapWidth,H,operandWidth]
    omega
  exact ⟨hChild,hRaw,hTable,hWrapper⟩

theorem profile_bound (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ) :
    GeneralPaperCachedPowerPreparation.profile primitive W lambda k≤
      131072*measure m lambda k Qv*(W+primitive (operandWidth m lambda k Qv)) := by
  let M := measure m lambda k Qv
  let H := operandWidth m lambda k Qv
  let F := W+primitive H
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let b := GeneralPaperStoredGeometricBase.construct f.unit f.fractionalBits k
  let t := GeneralPaperRoundedPowerTable.build f.unit f.fractionalBits b.number f.columns
  let e := f.fractionalBits+1-GeneralPaperStoredGeometricBase.decrementBits k
  have hb := sizes m lambda k Qv
  have hm := GeneralPaperSourcePreparationControls.metadata m lambda k Qv
  have hp := hm.fractionalBits
  have hc := hm.columns
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).1
  change f.fractionalBits≤128*M at hp
  change f.columns≤32*M at hc
  change k+128≤M at hM
  have he : e≤f.fractionalBits+1 := by dsimp only [e]; omega
  have hChild := Nat.mul_le_mul (show 64*(e+1)≤16384*M by omega)
    (Nat.add_le_add_left (hMono hb.baseChild) W)
  have hRaw := hMono hb.baseRaw
  have hTable := Nat.mul_le_mul (show 1024*(f.columns+1)≤65536*M by omega)
    (Nat.add_le_add_left (hMono hb.table) W)
  have hWrap := hMono hb.wrapper
  change 64*(e+1)*(W+primitive (8+2*e))≤16384*M*F at hChild
  change 1024*(f.columns+1)*(W+primitive (GeneralPaperPowerTableBounds.width f.fractionalBits f.columns b.number))≤65536*M*F at hTable
  have hW : W≤F := Nat.le_add_right _ _
  have hP : primitive H≤F := Nat.le_add_left _ _
  have hMF : F≤M*F := by
    have hh : 1≤M := by omega
    simpa only [one_mul] using Nat.mul_le_mul_right F hh
  unfold GeneralPaperCachedPowerPreparation.profile GeneralPaperStoredBasePrice.profile
  dsimp only
  change 64*(e+1)*(W+primitive (8+2*e))+
    17*primitive (GeneralPaperStoredBasePrice.rawWidth f.unit f.fractionalBits k (powerRun e))+96*W+
    1024*(f.columns+1)*(W+primitive (GeneralPaperPowerTableBounds.width f.fractionalBits f.columns b.number))+
    6*primitive (GeneralPaperCachedPowerPreparation.wrapWidth f.work b.work t.work)+96*W≤131072*M*F
  change _≤primitive H at hRaw hWrap
  nlinarith only [hChild,hRaw,hTable,hWrap,hW,hP,hMF]

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ)
    (c : GeneralPaperSourcePreparationCache.Cache) (hc : c=GeneralPaperSourcePreparationCache.specification m lambda k Qv) :
    (GeneralPaperCachedPowerPreparation.fromCache primitive W k c).2≤
      131072*measure m lambda k Qv*(W+primitive (operandWidth m lambda k Qv)) :=
  (GeneralPaperCachedPowerPreparation.work primitive hMono W m lambda k Qv c hc).trans (profile_bound primitive hMono W m lambda k Qv)

theorem arithmetic_profile (m lambda k Qv : ℕ) :
    GeneralPaperCachedPowerPreparation.arithmeticProfile lambda k≤262144*(measure m lambda k Qv+1)^2 := by
  let M := measure m lambda k Qv
  let f := GeneralPaperPowerPrecision.prepare lambda k
  have hm := GeneralPaperSourcePreparationControls.metadata m lambda k Qv
  have hp := hm.fractionalBits
  have hc := hm.columns
  change f.fractionalBits≤128*M at hp
  change f.columns≤32*M at hc
  have hMul := Nat.mul_le_mul hc (show 12*(f.fractionalBits+1)+194≤1536*M+206 by omega)
  unfold GeneralPaperCachedPowerPreparation.arithmeticProfile
  change 512*(f.fractionalBits+2)+f.columns*(12*(f.fractionalBits+1)+194)+144≤262144*(M+1)^2
  nlinarith only [hp,hMul,Nat.zero_le (M*M)]

theorem bit_work (model : RationalCostModel) (m lambda k Qv : ℕ)
    (c : GeneralPaperSourcePreparationCache.Cache) (hc : c=GeneralPaperSourcePreparationCache.specification m lambda k Qv) :
    (GeneralPaperCachedPowerPreparation.fromCache model.rat (GeneralPaperSourcePreparationControls.word m lambda k Qv) k c).2≤
      262144*measure m lambda k Qv*model.rat (operandWidth m lambda k Qv) := by
  have h := work model.rat model.monotone (GeneralPaperSourcePreparationControls.word m lambda k Qv) m lambda k Qv c hc
  have hW := GeneralPaperSourcePreparationControls.word_le_operand_width m lambda k Qv
  have hWidth : GeneralPaperSourcePreparationSizes.width m lambda k Qv≤operandWidth m lambda k Qv := by
    unfold GeneralPaperSourcePreparationSizes.width operandWidth
    omega
  have hw := (hW.trans hWidth).trans (model.word_le (operandWidth m lambda k Qv))
  calc
    _ ≤ 131072*measure m lambda k Qv*(GeneralPaperSourcePreparationControls.word m lambda k Qv+model.rat (operandWidth m lambda k Qv)) := h
    _ ≤ 131072*measure m lambda k Qv*(2*model.rat (operandWidth m lambda k Qv)) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

end Blotto.GeneralPaperPowerPreparationEnvelope
