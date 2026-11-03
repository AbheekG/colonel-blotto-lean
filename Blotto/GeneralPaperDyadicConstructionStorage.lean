import Blotto.GeneralPaperPreparationCacheStorage

/-! Literal records and structural frames of the native linear doubling
constructor. Every earlier power may be reserved simultaneously. Its word
bound derives from the constructed exponent, including zero. -/
namespace Blotto.GeneralPaperDyadicConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperScoreScaleParameters
set_option autoImplicit false
set_option maxHeartbeats 800000

def peak (W : ℕ) : ℕ → ℕ
  | 0 => GeneralPaperPreparationCacheStorage.powerFootprint W (powerRun 0)+natBits 0+128*W
  | n+1 => GeneralPaperPreparationCacheStorage.powerFootprint W (powerRun (n+1))+natBits (n+1)+128*W+peak W n

theorem bounded (W m lambda k Qv n : ℕ) (hn : n≤74+2*k) :
    peak W n≤(n+1)*(4*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+192*W) := by
  have hNat (e : ℕ) (he : e≤74+2*k) : natBits e≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    have h := GeneralPaperInitializerControlCounters.word_le_self e
    have hk := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).1
    unfold natBits GeneralPaperPowerPreparationEnvelope.operandWidth
    omega
  induction n with
  | zero =>
    have hp := GeneralPaperPreparationCacheStorage.dyadic W m lambda k Qv 0 hn
    have hw := hNat 0 hn
    change _≤(0+1)*(4*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+192*W)
    unfold peak
    omega
  | succ n ih =>
    have hp := GeneralPaperPreparationCacheStorage.dyadic W m lambda k Qv (n+1) hn
    have hw := hNat (n+1) hn
    have hi := ih (by omega)
    rw [peak]
    nlinarith only [hp,hw,hi]

def window (model : RationalCostModel) (W n : ℕ) : ℕ :=
  peak W n+(GeneralPaperDyadicPowerBits.run model.rat W n).2

theorem scratch (model : RationalCostModel) (W m lambda k Qv n : ℕ) (hn : n≤74+2*k) :
    (GeneralPaperDyadicPowerBits.run model.rat W n).2≤
      64*(n+1)*(W+model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := by
  have hWidth : 8+2*n≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    have hk := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).1
    unfold GeneralPaperPowerPreparationEnvelope.operandWidth
    omega
  exact (GeneralPaperDyadicPowerBits.work model.rat model.monotone W n).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hWidth) W))

theorem whole (model : RationalCostModel) (W m lambda k Qv n : ℕ) (hn : n≤74+2*k) :
    window model W n≤(n+1)*(4*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+192*W)+
      64*(n+1)*(W+model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) :=
  Nat.add_le_add (bounded W m lambda k Qv n hn) (scratch model W m lambda k Qv n hn)

end Blotto.GeneralPaperDyadicConstructionStorage
