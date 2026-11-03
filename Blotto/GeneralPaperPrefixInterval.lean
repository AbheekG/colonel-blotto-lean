import Blotto.GeneralPaperPreparedCDFProperties

/-! Exact integer interval numerators from a native prefix array. These
differences are formed before probability-mesh rounding and use the whole
block's stored total, including both signs of a signed alphabet.
-/
namespace Blotto.GeneralPaperPrefixInterval
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

def numerator {n : ℕ} (preparedPrefix : FixedArrayTable (n+1) ℕ) (lo hi : Fin (n+1)) : ℕ :=
  preparedPrefix.read hi-preparedPrefix.read lo

theorem numerator_le_total {n : ℕ} (values : FixedArrayTable n ℕ) (lo hi : Fin (n+1)) :
    numerator (GeneralPaperEpochPrefixArray.build values) lo hi≤
      (GeneralPaperEpochPrefixArray.build values).read (Fin.last n) :=
  (Nat.sub_le _ _).trans (GeneralPaperEpochPrefixQuery.read_le_total values hi)

theorem numerator_sum {n : ℕ} (values : FixedArrayTable n ℕ) (lo hi : Fin (n+1)) (hOrder : lo≤hi) :
    numerator (GeneralPaperEpochPrefixArray.build values) lo hi=
      ∑ r, if lo.val≤r.val ∧ r.val<hi.val then values.read r else 0 := by
  have hRanks : lo.val≤hi.val := hOrder
  have hEach (r : Fin n) : (if r.val<hi.val then values.read r else 0)=
      (if r.val<lo.val then values.read r else 0)+
        (if lo.val≤r.val ∧ r.val<hi.val then values.read r else 0) := by
    by_cases hLow : r.val<lo.val
    · have hHigh : r.val<hi.val := hLow.trans_le hRanks
      simp only [hLow,hHigh,show ¬lo.val≤r.val by omega,ite_true,ite_false,false_and,Nat.add_zero]
    · have hAbove : lo.val≤r.val := by omega
      by_cases hHigh : r.val<hi.val <;> simp only [hLow,hHigh,hAbove,ite_true,ite_false,true_and,Nat.zero_add]
  have hSum := Finset.sum_congr rfl (fun r (_ : r∈Finset.univ) => hEach r)
  rw [Finset.sum_add_distrib] at hSum
  have hLo := lo.isLt
  have hHi := hi.isLt
  change (GeneralPaperEpochPrefixArray.build values).read ⟨hi.val,by omega⟩-
    (GeneralPaperEpochPrefixArray.build values).read ⟨lo.val,by omega⟩= _
  rw [GeneralPaperEpochPrefixQuery.read_prefix values hi.val (by omega),
    GeneralPaperEpochPrefixQuery.read_prefix values lo.val (by omega)]
  unfold GeneralPaperEpochPrefixQuery.sumPrefix
  omega

theorem ratio_real {n : ℕ} (values : FixedArrayTable n ℕ) (lo hi : Fin (n+1)) (hOrder : lo≤hi) :
    (numerator (GeneralPaperEpochPrefixArray.build values) lo hi:ℝ)/
        ((GeneralPaperEpochPrefixArray.build values).read (Fin.last n):ℝ)=
      ((GeneralPaperEpochPrefixArray.build values).read hi:ℝ)/
          ((GeneralPaperEpochPrefixArray.build values).read (Fin.last n):ℝ)-
        ((GeneralPaperEpochPrefixArray.build values).read lo:ℝ)/
          ((GeneralPaperEpochPrefixArray.build values).read (Fin.last n):ℝ) := by
  rw [numerator,Nat.cast_sub (GeneralPaperRankedCDFQuery.prefix_monotone values hOrder),sub_div]

theorem lower_antitone {n : ℕ} (values : FixedArrayTable n ℕ) (hi : Fin (n+1)) :
    Antitone (fun lo => numerator (GeneralPaperEpochPrefixArray.build values) lo hi) := by
  intro small large hOrder
  have he := GeneralPaperRankedCDFQuery.prefix_monotone values hOrder
  change (GeneralPaperEpochPrefixArray.build values).read hi-(GeneralPaperEpochPrefixArray.build values).read large≤
    (GeneralPaperEpochPrefixArray.build values).read hi-(GeneralPaperEpochPrefixArray.build values).read small
  omega

theorem empty {n : ℕ} (preparedPrefix : FixedArrayTable (n+1) ℕ) (rank : Fin (n+1)) : numerator preparedPrefix rank rank=0 := by
  simp [numerator]

theorem full {n : ℕ} (values : FixedArrayTable n ℕ) :
    numerator (GeneralPaperEpochPrefixArray.build values) 0 (Fin.last n)=
      (GeneralPaperEpochPrefixArray.build values).read (Fin.last n) := by
  rw [numerator,GeneralPaperEpochPrefixArray.read_zero,Nat.sub_zero]

end Blotto.GeneralPaperPrefixInterval
