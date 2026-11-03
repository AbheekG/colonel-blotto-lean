import Blotto.GeneralPaperDyadicPowerBits
import Blotto.GeneralPaperInitializerControlCounters

/-! A bounded alignment power uses repeated squaring in the bit model.
The returned power, doubling count and legacy work field agree with the
native linear constructor; metadata is computed from the degree, without
replaying that constructor. The unit arithmetic path remains linear.
-/
namespace Blotto.GeneralPaperAlignmentPowerPrice
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def run (primitive : ℕ → ℕ) (W degree : ℕ) : GeneralPaperPowerCeiling.Result × ℕ :=
  let power := GeneralPaperNatPowerBits.run primitive W 2 degree
  (⟨power.1.power,degree,8*degree+2⟩,power.2+48*W+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 8 degree+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (8*degree) 2)

theorem data (primitive : ℕ → ℕ) (W degree : ℕ) :
    (run primitive W degree).1=GeneralPaperScoreScaleParameters.powerRun degree := by
  have hp := GeneralPaperScoreScaleParameters.power_data degree
  simp only [run,GeneralPaperNatPowerBits.data,(GeneralPaperNatPower.data 2 degree).1]
  cases he : GeneralPaperScoreScaleParameters.powerRun degree with
  | mk power doublings work =>
    rw [he] at hp
    dsimp only at hp
    rcases hp with ⟨rfl,rfl,rfl⟩
    rfl

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W degree : ℕ) :
    (run primitive W degree).2≤256*(binaryWordWidth degree+1)*(W+primitive (32+4*degree)) := by
  let L := 32+4*degree
  have hWord := GeneralPaperInitializerControlCounters.word_le_self degree
  have hMul := binaryWordWidth_mul 8 degree
  have hAdd := GeneralPaperRayOperandWidthEnvelope.word_add (8*degree) 2
  have h8 : binaryWordWidth 8=4 := by decide
  have h2 : binaryWordWidth 2=2 := by decide
  have ha := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) 8 degree L
    (by dsimp [L]; omega) (by dsimp [L]; omega) (by dsimp [L]; omega)
  have hb := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) (8*degree) 2 L
    (by dsimp [L]; omega) (by dsimp [L]; omega) (by dsimp [L]; omega)
  have hp := GeneralPaperNatPowerBits.work primitive hMono W 2 degree (by decide)
  have hWidth : GeneralPaperNatPowerOperands.width 2 degree≤L := by
    unfold GeneralPaperNatPowerOperands.width
    rw [h2]
    dsimp [L]
    omega
  have hi := hp.trans (Nat.mul_le_mul_left (64*(binaryWordWidth degree+1))
    (Nat.add_le_add_left (hMono hWidth) W))
  change _≤256*(binaryWordWidth degree+1)*(W+primitive L)
  change (GeneralPaperNatPowerBits.run primitive W 2 degree).2+48*W+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 8 degree+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (8*degree) 2≤_
  nlinarith only [hi,ha,hb,Nat.zero_le (binaryWordWidth degree)]

def arithmetic (degree : ℕ) : GeneralPaperPowerCeiling.Result × ℕ :=
  GeneralPaperDyadicPowerBits.run (fun _ => 1) 1 degree

theorem arithmetic_data (degree : ℕ) :
    (arithmetic degree).1=GeneralPaperScoreScaleParameters.powerRun degree :=
  GeneralPaperDyadicPowerBits.data _ _ _

theorem arithmetic_work (degree : ℕ) : (arithmetic degree).2≤128*(degree+1) := by
  have h := GeneralPaperDyadicPowerBits.work (fun _ => 1) (by intro a b h; rfl) 1 degree
  dsimp only [arithmetic]
  nlinarith only [h]

end Blotto.GeneralPaperAlignmentPowerPrice
