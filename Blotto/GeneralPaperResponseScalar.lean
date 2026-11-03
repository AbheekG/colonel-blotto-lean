import Blotto.GeneralPaperResponseOption

/-! Exact scalar shares for the selected physical response option against
every closed code. The greatest-threshold argument is the arbitrary-index
form of the retained finite-anchor scalar transport proof.
-/
namespace Blotto.GeneralPaperResponseScalar
open GeneralPaperCodeAlphabet GeneralPaperClosedAlphabet GeneralPaperResponseOption
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem scalar_share {ι : Type*} (bid : ι → ℝ) (label : ι) (y bump : ℝ)
    (hBelow : bid label≤y) (hGreatest : ∀ i, bid i≤y → bid i≤bid label)
    (hBump : 0<bump) (hGap : ∀ i, bid label<bid i → bid label+bump<bid i) (i : ι) :
    share y (bid i)=share (bid label+if bid label=y then 0 else bump) (bid i) := by
  rcases lt_trichotomy (bid i) (bid label) with hi|hi|hi
  · have ho := hi.trans_le hBelow
    have hb : bid i<bid label+if bid label=y then 0 else bump := by split_ifs <;> linarith
    simp only [share,ho,hb,ite_true]
  · by_cases he : bid label=y
    · simp [share,hi,he]
    · have hLabel : bid label<y := lt_of_le_of_ne hBelow he
      have hb : bid label<bid label+bump := by linarith only [hBump]
      simp only [hi,he,ite_false,share,hLabel,hb,ite_true]
  · have ho : y<bid i := lt_of_not_ge (fun h => (not_le_of_gt hi) (hGreatest i h))
    have hb : bid label+(if bid label=y then 0 else bump)<bid i := by
      split_ifs
      · simpa only [add_zero] using hi
      · exact hGap i hi
    simp [share,not_lt_of_gt ho,ne_of_lt ho,not_lt_of_gt hb,ne_of_lt hb]

theorem option_share (a : Alphabet) (m qbar : ℕ) (hm : 0<m) (hQ : 0<qbar)
    (y : ℝ) (hy : 0≤y) (hOne : y≤1) (i : Closed a) :
    share y (value a i:ℝ)=share ((option a y hy hOne).selected.physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C):ℝ) (value a i:ℝ) := by
  rw [physical_formula]
  apply scalar_share (fun j : Closed a => (value a j:ℝ)) (lower a y hy) y _ (lower_le a y hy)
  · intro j hj
    exact_mod_cast lower_greatest a y hy j hj
  · exact_mod_cast GeneralPaperTagBudgetTransfer.shift_positive m qbar a.C hm hQ a.scalePositive
  · intro j hj
    have hq : value a (lower a y hy)<value a j := by exact_mod_cast hj
    exact_mod_cast threshold_gap a (lower a y hy) j m qbar hm hQ hq

end Blotto.GeneralPaperResponseScalar
