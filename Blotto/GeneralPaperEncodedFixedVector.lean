import Blotto.GeneralPaperRoundUpdateStorage

/-! Fixed-vector storage counts owned payloads, entry references and one
descriptor. Rank values are bounded by their actual finite type. -/
namespace Blotto.GeneralPaperEncodedFixedVector
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def footprint {α : Type*} {n : ℕ} (W : ℕ) (encode : α → ℕ) (values : FixedArrayTable n α) : ℕ :=
  (∑ i,encode (values.read i))+n*W+32*W

theorem bounded {α : Type*} {n : ℕ} (W P : ℕ) (encode : α → ℕ) (values : FixedArrayTable n α)
    (he : ∀ i,encode (values.read i)≤P) : footprint W encode values≤n*(P+W)+32*W := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => he i)
  have hp : (∑ i,encode (values.read i))≤n*P := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hs
  unfold footprint
  nlinarith only [hp]

theorem bounded_length {α : Type*} {n : ℕ} (W P N : ℕ) (encode : α → ℕ) (values : FixedArrayTable n α)
    (hn : n≤N) (he : ∀ i,encode (values.read i)≤P) : footprint W encode values≤N*(P+W)+32*W :=
  (bounded W P encode values he).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)

def rankBits {J : ℕ} (i : Fin J) : ℕ := 1+binaryWordWidth i.val
def rankWord (J : ℕ) : ℕ := 1+binaryWordWidth J

theorem rank_bound {J : ℕ} (i : Fin J) : rankBits i≤rankWord J :=
  Nat.add_le_add_left (binaryWordWidth_mono i.isLt.le) 1

theorem rank_array {n J : ℕ} (W : ℕ) (values : FixedArrayTable n (Fin J)) :
    footprint W rankBits values≤n*(rankWord J+W)+32*W := bounded W _ rankBits values (fun i => rank_bound (values.read i))

theorem annotation (value cap : ℕ) (hc : value≤cap) : 1+binaryWordWidth value≤cap+2 := by
  have hw := GeneralPaperInitializerControlCounters.word_le_self value
  omega

end Blotto.GeneralPaperEncodedFixedVector
