import Blotto.GeneralPaperResponseScalar

/-! Complete response-row representation with exact symbolic budgets.
Each real deviation coordinate uses its greatest affordable closed code;
an open coordinate forces strict slack in the sum of lower thresholds.
-/
namespace Blotto.GeneralPaperContinuousResponseRow
open scoped BigOperators Classical
open GeneralPaperCodeAlphabet GeneralPaperResponseOption GeneralPaperClosedAlphabet
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem coordinate_le_one {m : ℕ} (B : ℚ) (hB : B≤1) (y : Allocation m) (hy : Blotto.Feasible (B:ℝ) y) (j : Fin m) : y j≤1 := by
  have hj := Finset.single_le_sum (f:=y) (fun i _ => hy.1 i) (Finset.mem_univ j)
  have hb : (B:ℝ)≤1 := by exact_mod_cast hB
  exact hj.trans (hy.2.trans hb)

noncomputable def fieldOption {m : ℕ} (a : Alphabet) (B : ℚ) (hB : B≤1) (y : Allocation m) (hy : Blotto.Feasible (B:ℝ) y) (j : Fin m) :=
  option a (y j) (hy.1 j) (coordinate_le_one B hB y hy j)

noncomputable def choices {m : ℕ} (a : Alphabet) (B : ℚ) (hB : B≤1) (y : Allocation m) (hy : Blotto.Feasible (B:ℝ) y) : FixedArrayTable m Choice :=
  FixedArrayTable.ofFn (fun j => (fieldOption a B hB y hy j).selected)

noncomputable def codes {m : ℕ} (a : Alphabet) (B : ℚ) (hB : B≤1) (y : Allocation m) (hy : Blotto.Feasible (B:ℝ) y) : FixedArrayTable m ℕ :=
  FixedArrayTable.ofFn (fun j => (fieldOption a B hB y hy j).code)

theorem decoded {m : ℕ} (a : Alphabet) (B : ℚ) (hB : B≤1) (y : Allocation m) (hy : Blotto.Feasible (B:ℝ) y) (j : Fin m) :
    (GeneralPaperCodeDecode.decode a true ((codes a B hB y hy).read j)).choice=some ((choices a B hB y hy).read j) := by
  simp only [codes,choices,FixedArrayTable.read_ofFn]
  exact (fieldOption a B hB y hy j).decoded

theorem code_bound {m : ℕ} (a : Alphabet) (B : ℚ) (hB : B≤1) (y : Allocation m) (hy : Blotto.Feasible (B:ℝ) y) (j : Fin m) :
    (codes a B hB y hy).read j<2^a.lambda := by
  rw [codes,FixedArrayTable.read_ofFn]
  exact GeneralPaperResponseOption.code_bound a (y j) (hy.1 j) _

theorem thresholds_below {m : ℕ} (a : Alphabet) (B : ℚ) (hB : B≤1) (y : Allocation m) (hy : Blotto.Feasible (B:ℝ) y) (j : Fin m) :
    (((choices a B hB y hy).read j).threshold.value:ℝ)≤y j := by
  rw [choices,FixedArrayTable.read_ofFn]
  exact below a (y j) (hy.1 j) _

theorem threshold_sum_le {m : ℕ} (a : Alphabet) (B : ℚ) (hB : B≤1) (y : Allocation m) (hy : Blotto.Feasible (B:ℝ) y) :
    (∑ j, ((choices a B hB y hy).read j).threshold.value)≤B := by
  have hs := (Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => thresholds_below a B hB y hy j)).trans hy.2
  exact_mod_cast hs

theorem open_sum_strict {m : ℕ} (a : Alphabet) (B : ℚ) (hB : B≤1) (y : Allocation m) (hy : Blotto.Feasible (B:ℝ) y)
    (j : Fin m) (hj : ((choices a B hB y hy).read j).opened=true) :
    (∑ i, ((choices a B hB y hy).read i).threshold.value)<B := by
  have hstrict : (((choices a B hB y hy).read j).threshold.value:ℝ)<y j := by
    rw [choices,FixedArrayTable.read_ofFn] at hj ⊢
    exact opened_strict a (y j) (hy.1 j) _ hj
  have hs := Finset.sum_lt_sum (fun i (_ : i∈Finset.univ) => thresholds_below a B hB y hy i) ⟨j,Finset.mem_univ _,hstrict⟩
  have he := hs.trans_le hy.2
  exact_mod_cast he

theorem tag_budget {m : ℕ} (a : Alphabet) (B : ℚ) (hB : B≤1) (y : Allocation m) (hy : Blotto.Feasible (B:ℝ) y) :
    (∑ j, ((choices a B hB y hy).read j).tag)≤GeneralPaperResponseTag.budget B := by
  have he : GeneralPaperTagBudgetTransfer.rowTag (fun j => ((choices a B hB y hy).read j).threshold)
      (fun j => ((choices a B hB y hy).read j).opened)≤GeneralPaperResponseTag.budget B := by
    rw [GeneralPaperTagBudgetTransfer.tag_budget_iff]
    by_cases hs : (∑ j, ((choices a B hB y hy).read j).threshold.value)<B
    · exact Or.inl hs
    · refine Or.inr ⟨le_antisymm (threshold_sum_le a B hB y hy) (le_of_not_gt hs),?_⟩
      intro j
      cases hf : ((choices a B hB y hy).read j).opened with
      | false => rfl
      | true => exact (hs (open_sum_strict a B hB y hy j hf)).elim
  simpa only [GeneralPaperTagBudgetTransfer.rowTag,List.sum_ofFn,Choice.tag] using he

theorem share_exact {m : ℕ} (a : Alphabet) (B : ℚ) (hB : B≤1) (y : Allocation m) (hy : Blotto.Feasible (B:ℝ) y)
    (qbar : ℕ) (hm : 0<m) (hQ : 0<qbar) (j : Fin m) (i : Closed a) :
    share (y j) (value a i:ℝ)=
      share (((choices a B hB y hy).read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C):ℝ) (value a i:ℝ) := by
  rw [choices,FixedArrayTable.read_ofFn]
  exact GeneralPaperResponseScalar.option_share a m qbar hm hQ (y j) (hy.1 j) _ i

end Blotto.GeneralPaperContinuousResponseRow
