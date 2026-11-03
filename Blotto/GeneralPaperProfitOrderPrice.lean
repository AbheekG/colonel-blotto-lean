import Blotto.GeneralPaperNaturalOrderPrice

/-! Instantiate the complete ordering pass with the actual fixed profit
grid points. Their proved bound discharges every comparison-size premise.
This pass consumes generated points; point generation and array preparation
are still separate phases. Its constructed reference word covers capacities.
-/
namespace Blotto.GeneralPaperProfitOrderPrice
open GeneralPaperProfitGridPoints
set_option autoImplicit false
set_option maxHeartbeats 6000000

def capacity (w B : ℕ) : ℕ := (B+1)*(w+1)+3
def word (w B : ℕ) : ℕ := 128+8*binaryWordWidth (capacity w B)

theorem data (primitive : ℕ → ℕ) (W w B : ℕ) :
    (GeneralPaperNaturalOrderPrice.run primitive W (2*denominator w B) (points w B)).1=
      GeneralPaperProfitGridPrepare.ordered w B := GeneralPaperNaturalOrderPrice.data _ _ _ _

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W w B : ℕ) :
    (GeneralPaperNaturalOrderPrice.run primitive W (2*denominator w B) (points w B)).2≤
      GeneralPaperNaturalOrderPrice.profile ((B+1)*w) W (primitive (1+binaryWordWidth (2*denominator w B))) := by
  have h := GeneralPaperNaturalOrderPrice.work primitive hMono W (2*denominator w B) (points w B)
    (fun x hx => points_bound w B x hx)
  simpa only [points_length] using h

theorem points_capacity (w B : ℕ) : (points w B).length+3≤capacity w B := by
  rw [points_length]
  unfold capacity
  nlinarith only [Nat.zero_le (B+1)]

theorem bounded (w B n : ℕ) (hn : n≤128*capacity w B+128) : binaryWordWidth n≤word w B := by
  have hPos : 0<capacity w B := by unfold capacity; omega
  have hBound : n≤256*capacity w B := by omega
  have hm := binaryWordWidth_mul 256 (capacity w B)
  have hs := binaryWordWidth_mono hBound
  have h256 : binaryWordWidth 256=9 := by decide
  unfold word
  omega

theorem reference_indices (w B n : ℕ) (hn : n≤(points w B).length+2) : binaryWordWidth (n+1)≤word w B := by
  apply bounded
  have hp := points_capacity w B
  omega

theorem generator_indices (w B : ℕ) : binaryWordWidth (w+1)≤word w B ∧ binaryWordWidth (B+1)≤word w B := by
  have hw : w+1≤(B+1)*(w+1) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (w+1) (show 1≤B+1 by omega)
  have hb : B+1≤(B+1)*(w+1) := by
    simpa only [mul_one] using Nat.mul_le_mul_left (B+1) (show 1≤w+1 by omega)
  constructor <;> apply bounded <;> unfold capacity <;> omega

theorem sorting_ceiling_controls (primitive : ℕ → ℕ) (w B p : ℕ) (hp : 0<p) :
    let target := (points w B).length+3
    binaryWordWidth ((GeneralPaperPowerCeilingBits.loop primitive (word w B) target p hp).1.doublings+1)≤word w B ∧
      binaryWordWidth ((GeneralPaperPowerCeilingBits.loop primitive (word w B) target p hp).1.work+192)≤word w B := by
  have ht := points_capacity w B
  have hi := binaryWordWidth_mono ht
  have hs := GeneralPaperInitializerControlCounters.word_le_self (binaryWordWidth ((points w B).length+3)+1)
  apply GeneralPaperParameterCounterWords.ceiling
  unfold word
  omega

theorem scaled_metadata (q w B : ℕ) : binaryWordWidth ((GeneralPaperProfitGridPrepare.prepare q w B).scaledWork+128)≤word w B := by
  have hs := GeneralPaperProfitGridPrepare.size_bound q w B
  have hw := GeneralPaperProfitGridPrepare.scaled_work q w B
  apply bounded
  unfold capacity
  nlinarith only [hs,hw,Nat.zero_le B,Nat.zero_le w]

end Blotto.GeneralPaperProfitOrderPrice
