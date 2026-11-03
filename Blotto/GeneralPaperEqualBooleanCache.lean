import Blotto.GeneralPaperBooleanCategoricalSelect

/-! Fixed-width encodings of the retained denominator/counts, cached labels
and a unary ruler for the fresh scan. These are prepared once; a draw never
re-encodes a denominator/count or constructs an expanded categorical range. -/
namespace Blotto.GeneralPaperEqualBooleanCache
open scoped BigOperators
open GeneralPaperEqualPreparedCache
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem denominator_fits {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) : p.D < 2 ^ (p.rangeBits + 1) := by
  have h := UniformNatRejection.width_upper p.D
  rw [← p.rangeBits_correct] at h
  have hp := Nat.two_pow_pos p.rangeBits
  rw [pow_succ]
  omega

theorem count_fits {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (i : Fin (count l)) : p.counts.read i < 2 ^ (p.rangeBits + 1) :=
  (counts_bounded p i).trans_lt (denominator_fits p)

def word {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (i : Fin (count l)) : FixedBinaryWord (p.rangeBits + 1) :=
  FixedBinaryWord.ofNat (p.rangeBits + 1) (p.counts.read i)

theorem word_value {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (i : Fin (count l)) : (word p i).value = p.counts.read i :=
  FixedBinaryWord.value_ofNat _ _ (count_fits p i)

structure Cache {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) where
  denominator : FixedBinaryWord (p.rangeBits + 1)
  denominator_value : denominator.value = p.D
  rows : List (Fin (count l) × FixedBinaryWord (p.rangeBits + 1))
  rows_correct : rows = List.ofFn (fun i => (i, word p i))
  ruler : List Unit
  ruler_length : ruler.length = p.rangeBits

def prepare {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) : Cache p :=
  ⟨FixedBinaryWord.ofNat (p.rangeBits + 1) p.D, FixedBinaryWord.value_ofNat _ _ (denominator_fits p),
    List.ofFn (fun i => (i, word p i)), rfl, List.replicate p.rangeBits (), by simp⟩

theorem rows_length {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) : c.rows.length = count l := by rw [c.rows_correct, List.length_ofFn]

def payload {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) : ℕ :=
  c.denominator.bits.length + (c.rows.map (fun row => row.2.bits.length)).sum + c.ruler.length

theorem payload_eq {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) : payload c = (count l + 1) * (p.rangeBits + 1) + p.rangeBits := by
  simp only [payload, c.denominator.size, c.rows_correct, List.map_ofFn, FixedBinaryWord.size,
    List.sum_ofFn, Function.comp_def, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, c.ruler_length]
  ring

theorem selection_data {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (w : FixedBinaryWord (p.rangeBits + 1)) (rank : Fin p.D)
    (hv : w.value = rank.val) : (GeneralPaperBooleanCategoricalSelect.run c.rows w).1 = some (select p rank) := by
  have hc : (fun i => (word p i).value) = p.counts.read := funext (word_value p)
  have hs : (∑ i, (word p i).value) = p.D := by simp only [word_value]; exact counts_sum p
  have h := GeneralPaperBooleanCategoricalSelect.data (count l) id (word p) w (rank.cast hs.symm) hv
  simp only [id_eq] at h
  rw [← c.rows_correct] at h
  change _ = some _ at h
  convert h using 2
  have he (a b : Fin (count l) → ℕ) (hab : a = b)
      (i : Fin (∑ j, a j)) (j : Fin (∑ j, b j)) (hij : i.val = j.val) :
      GeneralPaperEqualCategoricalSelector.select a i = GeneralPaperEqualCategoricalSelector.select b j := by
    subst b
    congr 1
    exact Fin.ext hij
  exact he _ _ hc.symm _ _ rfl

end Blotto.GeneralPaperEqualBooleanCache
