import Blotto.GeneralPaperInitializerControlBits

/-! Every reached ceiling return and raw return-counter update fits the
local control word. Integer/rational products have their separate actual
primitive prices; these bounds concern the linear control/frame additions.
-/
namespace Blotto.GeneralPaperInitializerControlCounters
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem word_le_self (n : ℕ) : binaryWordWidth n≤n+1 := by
  apply binaryWordWidth_le_of_lt_pow (Nat.succ_pos n)
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have hp := Nat.two_pow_pos (n+1)
    omega

theorem counter_width (n : ℕ) : binaryWordWidth (12*n+194)≤n+20 := by
  have hm := binaryWordWidth_mul 12 n
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (12*n) 194
  have hn := word_le_self n
  have h12 : binaryWordWidth 12=4 := by decide
  have h194 : binaryWordWidth 194=8 := by decide
  omega

theorem loop_counters (primitive : ℕ → ℕ) (W target p : ℕ) (hp : 0<p)
    (hW : binaryWordWidth target+64≤W) :
    binaryWordWidth ((GeneralPaperPowerCeilingBits.loop primitive W target p hp).1.doublings+1)≤W ∧
    binaryWordWidth ((GeneralPaperPowerCeilingBits.loop primitive W target p hp).1.work+192)≤W := by
  rw [GeneralPaperPowerCeilingBits.loop_data]
  have hd := GeneralPaperPowerCeiling.loop_depth target p hp
  have hw := (GeneralPaperPowerCeiling.loop_spec target p hp).2.2.2.2
  have hCount := word_le_self ((GeneralPaperPowerCeiling.loop target p hp).doublings+1)
  have hWork : (GeneralPaperPowerCeiling.loop target p hp).work+192≤12*binaryWordWidth target+194 := by omega
  have hc := (binaryWordWidth_mono hWork).trans (counter_width (binaryWordWidth target))
  constructor <;> omega

end Blotto.GeneralPaperInitializerControlCounters
