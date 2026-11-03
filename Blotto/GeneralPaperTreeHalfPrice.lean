import Blotto.GeneralPaperPricedListSplit

/-! A retained dyadic span is halved by the existing midpoint routine.
The real-RAM implementation uses bounded arithmetic division, and the bit
implementation uses integer halving. No local power table is rebuilt. -/
namespace Blotto.GeneralPaperTreeHalfPrice
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run (bits : Bool) (primitive : ℕ → ℕ) (W height span : ℕ) : ℕ × ℕ :=
  let half := GeneralPaperRankMidpointPrice.run bits primitive W (height+2) 0 span
  (half.1.quotient,half.2+64*W+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) height 2)

theorem data (bits : Bool) (primitive : ℕ → ℕ) (W height span : ℕ) (hSpan : span=2^(height+1)) :
    (run bits primitive W height span).1=2^height := by
  have hs : span<2^(height+2) := by rw [hSpan,show height+2=(height+1)+1 by omega,pow_succ]; have := Nat.two_pow_pos (height+1); omega
  have hd := GeneralPaperRankMidpointPrice.data bits primitive W span (height+2) 0 span (Nat.zero_le _) (Nat.le_refl _) hs
  have hq := GeneralPaperFastConstructedDivision.quotient_data span 2 (height+2) (by decide) (by omega)
  have he : (GeneralPaperRankMidpoint.midpoint (height+2) 0 span).quotient=span/2 := by
    simpa only [GeneralPaperRankMidpoint.midpoint,Nat.cast_zero,zero_add,Nat.cast_ofNat] using hq
  change (GeneralPaperRankMidpointPrice.run bits primitive W (height+2) 0 span).1.quotient=_
  rw [hd,GeneralPaperRankMidpointPrice.specification,he,hSpan,pow_succ,Nat.mul_div_left _ (by decide : 0<2)]

def width (height : ℕ) : ℕ := GeneralPaperRankOperands.width (height+2) 0

theorem bit_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W height span : ℕ) (hSpan : span=2^(height+1)) :
    (run true primitive W height span).2≤10*primitive (width height)+128*W := by
  have hs : span<2^(height+2) := by rw [hSpan,show height+2=(height+1)+1 by omega,pow_succ]; have := Nat.two_pow_pos (height+1); omega
  have h := GeneralPaperRankOperands.midpoint_work primitive hMono W span (height+2) 0 0 span (Nat.zero_le _) (Nat.le_refl _) hs
  have hw := GeneralPaperInitializerControlCounters.word_le_self (height+2)
  have hh := binaryWordWidth_mono (show height≤height+2 by omega)
  have h2 : binaryWordWidth 2=2 := by decide
  have ha := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) height 2 (width height)
    (by unfold width GeneralPaperRankOperands.width; omega)
    (by unfold width GeneralPaperRankOperands.width; omega)
    (by unfold width GeneralPaperRankOperands.width; omega)
  change (GeneralPaperRankMidpointPrice.run true primitive W (height+2) 0 span).2+64*W+_≤_
  change _≤8*primitive (width height)+64*W at h
  omega

theorem arithmetic_work (height span : ℕ) : (run false (fun _ => 1) 1 height span).2=12*height+172 := by
  change (GeneralPaperRankMidpointPrice.run false (fun _ => 1) 1 (height+2) 0 span).2+64+2=12*height+172
  rw [GeneralPaperRankMidpointPrice.arithmetic_work]
  ring

end Blotto.GeneralPaperTreeHalfPrice
