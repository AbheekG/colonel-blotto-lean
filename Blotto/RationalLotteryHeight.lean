import Blotto.RationalLotterySwap
import Blotto.RationalThreeInputHeight
import Blotto.RationalInterpolationCode
import Blotto.DyadicMidpointHeight

/-! Uniform reduced-word height certificates for native segment tables.
Assembly preserves every slot, including zero weights and padding. -/

namespace Blotto.RationalSegmentLottery

def HeightAt {n k : ℕ} (l : RationalSegmentLottery n k) (s : ℕ) : Prop :=
  (∀ slot, RationalHeight (l.weight slot) s) ∧
    (∀ slot j, RationalHeight (l.P slot j) s ∧ RationalHeight (l.Q slot j) s)

theorem HeightAt.mono {n k : ℕ} {l : RationalSegmentLottery n k} {s t : ℕ}
    (h : l.HeightAt s) (hst : s ≤ t) : l.HeightAt t :=
  ⟨fun slot => (h.1 slot).mono hst, fun slot j => ⟨(h.2 slot j).1.mono hst, (h.2 slot j).2.mono hst⟩⟩

theorem HeightAt.padRight {n k : ℕ} {l : RationalSegmentLottery n k} {s : ℕ}
    (h : l.HeightAt s) (hs : 2 ≤ s) (m : ℕ) (fallback : Fin k) :
    (l.padRight m fallback).HeightAt s := by
  constructor
  · intro slot
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa [RationalSegmentLottery.padRight] using h.1 j
    · intro j
      simpa [RationalSegmentLottery.padRight] using
        (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  · intro slot j
    refine Fin.addCases ?_ ?_ slot
    · intro a; simpa [RationalSegmentLottery.padRight] using h.2 a j
    · intro a; simpa [RationalSegmentLottery.padRight] using h.2 fallback j

theorem HeightAt.binary {n k m : ℕ} {l : RationalSegmentLottery n k}
    {t : RationalSegmentLottery n m} {s : ℕ} (hl : l.HeightAt s) (ht : t.HeightAt s)
    (hs : 2 ≤ s) (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (hP : RationalHeight p s) :
    (binary p hp l t).HeightAt (expressionHeightBudget s 2) := by
  have hOne : RationalHeight (1 : ℚ) s :=
    (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hSub := hOne.sub hP
  have hSize : 3 * s + 1 ≤ expressionHeightBudget s 2 := by norm_num [expressionHeightBudget]; omega
  have hBase := expressionHeightBudget_ge_input s 2
  constructor
  · intro slot
    refine Fin.addCases ?_ ?_ slot
    · intro j
      have h := (hP.mul (hl.1 j)).mono (by omega : s + s ≤ expressionHeightBudget s 2)
      simpa [RationalSegmentLottery.binary] using h
    · intro j
      have h := (hSub.mul (ht.1 j)).mono (by omega : s + s + 1 + s ≤ expressionHeightBudget s 2)
      simpa [RationalSegmentLottery.binary] using h
  · intro slot j
    refine Fin.addCases ?_ ?_ slot
    · intro a; simpa [RationalSegmentLottery.binary] using And.intro ((hl.2 a j).1.mono hBase) ((hl.2 a j).2.mono hBase)
    · intro a; simpa [RationalSegmentLottery.binary] using And.intro ((ht.2 a j).1.mono hBase) ((ht.2 a j).2.mono hBase)

theorem HeightAt.shiftThird {k : ℕ} {l : RationalSegmentLottery 3 k} {s : ℕ}
    (h : l.HeightAt s) (x : ℚ) (hx : RationalHeight x s) :
    (l.shiftThird x).HeightAt (expressionHeightBudget s 1) := by
  have hm := expressionHeightBudget_ge_input s 1
  have he : expressionHeightBudget s 1 = s + s + 1 := by norm_num [expressionHeightBudget]; omega
  constructor
  · intro slot; exact (h.1 slot).mono hm
  · intro slot j
    fin_cases j
    · exact ⟨(h.2 slot 0).1.mono hm, (h.2 slot 0).2.mono hm⟩
    · exact ⟨(h.2 slot 1).1.mono hm, (h.2 slot 1).2.mono hm⟩
    · simpa [RationalSegmentLottery.shiftThird, he] using
        And.intro ((h.2 slot 2).1.add hx) ((h.2 slot 2).2.add hx)

theorem HeightAt.swapFirst {k : ℕ} {l : RationalSegmentLottery 3 k} {s : ℕ}
    (h : l.HeightAt s) : l.swapFirst.HeightAt s := by
  constructor
  · exact h.1
  · intro slot j
    fin_cases j
    · exact h.2 slot 1
    · exact h.2 slot 0
    · exact h.2 slot 2

theorem HeightAt.point {n k : ℕ} {l : RationalSegmentLottery n k} {s : ℕ}
    (h : l.HeightAt s) (hs : 2 ≤ s) (K : ℕ) (slot : Fin k) (bits : Fin K → Bool) (j : Fin n) :
    RationalHeight (l.point K slot bits j) (expressionHeightBudget (max s (K + 2)) 3) := by
  have hP := (h.2 slot j).1.mono (le_max_left s (K + 2))
  have hQ := (h.2 slot j).2.mono (le_max_left s (K + 2))
  have hT := (dyadicMidpointSample_height K bits).mono (le_max_right s (K + 2))
  exact RationalInterpolationCode.output_height _ _ _ _ (hs.trans (le_max_left _ _)) hP hQ hT

end Blotto.RationalSegmentLottery
