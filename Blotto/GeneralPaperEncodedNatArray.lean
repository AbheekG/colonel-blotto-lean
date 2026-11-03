import Blotto.GeneralPaperEncodedDPStorage

/-! Payload, entry references and descriptor space of one retained native
natural array. Every bound comes from its fixed length and literal entries. -/
namespace Blotto.GeneralPaperEncodedNatArray
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

def payload {n : ℕ} (values : FixedArrayTable n ℕ) : ℕ := ∑ i, (1+binaryWordWidth (values.read i))
def footprint {n : ℕ} (W : ℕ) (values : FixedArrayTable n ℕ) : ℕ := payload values+n*W+32*W

theorem bounded {n : ℕ} (W H : ℕ) (values : FixedArrayTable n ℕ) (h : ∀ i,1+binaryWordWidth (values.read i)≤H) :
    footprint W values≤n*(H+W)+32*W := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => h i)
  have hb : payload values≤n*H := by
    simpa only [payload,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hs
  unfold footprint
  nlinarith only [hb]

theorem bounded_length {n : ℕ} (W H N : ℕ) (values : FixedArrayTable n ℕ) (hn : n≤N)
    (h : ∀ i,1+binaryWordWidth (values.read i)≤H) : footprint W values≤N*(H+W)+32*W :=
  (bounded W H values h).trans (Nat.add_le_add_right (Nat.mul_le_mul_right (H+W) hn) _)

theorem level {n : ℕ} (W m lambda k Qv : ℕ) (values : FixedArrayTable n ℕ)
    (h : ∀ i,values.read i≤GeneralPaperPowerPrecision.levelBound lambda k) :
    footprint W values≤n*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+32*W :=
  bounded W _ values (fun i => (Nat.add_le_add_left (binaryWordWidth_mono (h i)) 1).trans
    (GeneralPaperFreshMassPrice.offset_width m lambda k Qv))

end Blotto.GeneralPaperEncodedNatArray
