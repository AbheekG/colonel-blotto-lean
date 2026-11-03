import Blotto.GeneralPaperCodePhysicalOrder

/-! Literal code comparisons reproduce canonical two-player shares. Ties,
including two zero bids, remain half ties. These are exact value identities
for actually decoded choices, before any CDF approximation or score error.
-/
namespace Blotto.GeneralPaperCodePayoff
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def codeShare (c d : ℕ) : ℝ := if d<c then 1 else if c=d then 1/2 else 0

theorem physical_equal (a : Alphabet) (responseX responseY : Bool) (c d : ℕ) (x y : Choice)
    (hX : (decode a responseX c).choice=some x) (hY : (decode a responseY d).choice=some y)
    (hCode : c=d) (delta : ℚ) : x.physical delta=y.physical delta := by
  have ht := (GeneralPaperCodeStrictOrder.code_eq_iff_tag_eq a responseX responseY c d x y hX hY).mp hCode
  have hValue : x.threshold.value=y.threshold.value := congrArg GeneralPaperResponseTag.Tag.threshold ht
  have hFlag : x.opened=y.opened := congrArg GeneralPaperResponseTag.Tag.opened ht
  unfold Choice.physical
  rw [hValue,hFlag]

theorem share_exact (a : Alphabet) (responseX responseY : Bool) (c d : ℕ) (x y : Choice)
    (hX : (decode a responseX c).choice=some x) (hY : (decode a responseY d).choice=some y)
    (m qbar : ℕ) (hm : 0<m) (hQ : 0<qbar) :
    share (x.physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C):ℝ)
      (y.physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C):ℝ)=codeShare c d := by
  rcases lt_trichotomy c d with hLt|hEq|hGt
  · have hp := GeneralPaperCodePhysicalOrder.selected_physical_strict a responseX responseY c d x y hX hY hLt m qbar hm hQ
    have hr := (Rat.cast_lt (K:=ℝ)).mpr hp
    simp only [share,codeShare,not_lt.mpr hLt.le,ite_false,hLt.ne,hr.ne,not_lt.mpr hr.le]
  · have he := physical_equal a responseX responseY c d x y hX hY hEq (GeneralPaperTagBudgetTransfer.shift m qbar a.C)
    have hr : (x.physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C):ℝ)=
      (y.physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C):ℝ) := congrArg (fun r : ℚ => (r:ℝ)) he
    simp only [hEq,codeShare,lt_self_iff_false,ite_false,ite_true,hr,share_tie]
  · have hp := GeneralPaperCodePhysicalOrder.selected_physical_strict a responseY responseX d c y x hY hX hGt m qbar hm hQ
    have hr := (Rat.cast_lt (K:=ℝ)).mpr hp
    simp only [share,codeShare,hGt,hr,ite_true]

theorem code_zero_tie : codeShare 0 0=1/2 := by simp only [codeShare,lt_self_iff_false,ite_false,ite_true]

theorem zero_physical (a : Alphabet) (delta : ℚ) : (⟨grid a 0,false⟩:Choice).physical delta=0 := by
  simp only [Choice.physical,grid_zero,Bool.false_eq_true,ite_false,add_zero]

theorem row_payoff_exact (a : Alphabet) (responseX responseY : Bool) (m qbar : ℕ) (hm : 0<m) (hQ : 0<qbar)
    (v : Values m) (c d : Fin m → ℕ) (x y : Fin m → Choice)
    (hX : ∀ j, (decode a responseX (c j)).choice=some (x j))
    (hY : ∀ j, (decode a responseY (d j)).choice=some (y j)) :
    payoff v (fun j => ((x j).physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C):ℝ))
      (fun j => ((y j).physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C):ℝ))=
      ∑ j, v.weight j*codeShare (c j) (d j) := by
  unfold payoff
  apply Finset.sum_congr rfl
  intro j _
  rw [share_exact a responseX responseY (c j) (d j) (x j) (y j) (hX j) (hY j) m qbar hm hQ]

end Blotto.GeneralPaperCodePayoff
