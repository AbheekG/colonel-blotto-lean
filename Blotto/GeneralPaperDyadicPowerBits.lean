import Blotto.GeneralPaperNatPowerBits
import Blotto.GeneralPaperScoreScaleParameters

/-! Price the existing linear doubling constructor of dyadic constants.
The power, doubling count and work field are exactly the native result.
-/
namespace Blotto.GeneralPaperDyadicPowerBits
set_option autoImplicit false

def run (primitive : ℕ → ℕ) (W : ℕ) : ℕ → GeneralPaperPowerCeiling.Result × ℕ
  | 0 => (⟨1,0,2⟩,16*W)
  | n+1 =>
      let earlier := run primitive W n
      (⟨2*earlier.1.power,earlier.1.doublings+1,earlier.1.work+8⟩,
        earlier.2+32*W+GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 earlier.1.power)

theorem data (primitive : ℕ → ℕ) (W n : ℕ) :
    (run primitive W n).1=GeneralPaperScoreScaleParameters.powerRun n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run,GeneralPaperScoreScaleParameters.powerRun,ih]

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W n : ℕ) :
    (run primitive W n).2≤64*(n+1)*(W+primitive (8+2*n)) := by
  induction n with
  | zero => change 16*W≤64*(0+1)*(W+primitive (8+2*0)); omega
  | succ n ih =>
    let L := 8+2*(n+1)
    let P := primitive L
    have hm := binaryWordWidth_mul 2 (run primitive W n).1.power
    have hp : binaryWordWidth (run primitive W n).1.power≤1+2*n := by
      rw [data,(GeneralPaperScoreScaleParameters.power_data n).1]
      simpa only [show binaryWordWidth 2=2 by decide,Nat.mul_comm] using GeneralPaperNatPowerOperands.power_width 2 n
    have h2 : binaryWordWidth 2=2 := by decide
    have hb := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b)
      2 (run primitive W n).1.power L (by dsimp [L]; omega) (by dsimp [L]; omega) (by dsimp [L]; omega)
    have hPrice := hMono (show 8+2*n≤L by dsimp [L]; omega)
    have hi := ih.trans (Nat.mul_le_mul_left (64*(n+1)) (Nat.add_le_add_left hPrice W))
    change (run primitive W n).2+32*W+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 (run primitive W n).1.power≤
        64*(n+1+1)*(W+P)
    change _≤2*P at hb
    change (run primitive W n).2≤64*(n+1)*(W+P) at hi
    nlinarith only [hi,hb]

end Blotto.GeneralPaperDyadicPowerBits
