import Blotto.GeneralPaperEqualCachedTraceLaw
import Blotto.PRGRealRAMExecution

/-! A single-uniform cumulative categorical scan. It subtracts the current
weight on each unsuccessful comparison, using the same original uniform;
the last remaining label is returned without another comparison. -/
namespace Blotto.GeneralPaperRealCumulativeChoice
open MeasureTheory Set
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 700000

noncomputable def select : (k : ℕ) → (Fin (k + 1) → ℝ) → ℝ → Fin (k + 1)
  | 0, _, _ => 0
  | k + 1, w, u => if u < w 0 then 0 else (select k (fun i => w i.succ) (u - w 0)).succ

noncomputable def lower : (k : ℕ) → (Fin (k + 1) → ℝ) → Fin (k + 1) → ℝ
  | 0, _, _ => 0
  | k + 1, w, i => Fin.cases 0 (fun j => w 0 + lower k (fun a => w a.succ) j) i

theorem lower_nonnegative (k : ℕ) (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i) (i : Fin (k + 1)) :
    0 ≤ lower k w i := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_rfl
    · exact add_nonneg (hw 0) (ih _ (fun a => hw a.succ) j)

theorem upper_le_sum (k : ℕ) (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i) (i : Fin (k + 1)) :
    lower k w i + w i ≤ ∑ j, w j := by
  induction k with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    simp [lower]
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun j => ?_) i
    · have h : 0 ≤ ∑ j : Fin (k + 1), w j.succ := Finset.sum_nonneg (fun j _ => hw j.succ)
      change 0 + w 0 ≤ _
      linarith only [h]
    · have h := ih (fun a => w a.succ) (fun a => hw a.succ) j
      change w 0 + lower k (fun a => w a.succ) j + w j.succ ≤ _
      linarith only [h]

theorem fiber (k : ℕ) (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (u : ℝ) (hu : u ∈ Ico 0 (∑ j, w j)) (i : Fin (k + 1)) :
    select k w u = i ↔ u ∈ Ico (lower k w i) (lower k w i + w i) := by
  induction k generalizing u with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    simpa [select, lower, Fin.sum_univ_succ] using hu
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if u < w 0 then 0 else (select k (fun a => w a.succ) (u - w 0)).succ) = 0 ↔ _
      by_cases h : u < w 0
      · simpa [h, lower] using hu.1
      · simp [h, lower]
    · change (if u < w 0 then 0 else (select k (fun a => w a.succ) (u - w 0)).succ) = j.succ ↔ _
      have hLower := lower_nonnegative k (fun a => w a.succ) (fun a => hw a.succ) j
      by_cases h : u < w 0
      · have hn : (0 : Fin (k + 1 + 1)) ≠ j.succ := Ne.symm (Fin.succ_ne_zero j)
        simp only [h, ite_true, hn, lower, Fin.cases_succ, mem_Ico, false_iff]
        intro hh
        linarith only [h, hLower, hh.1]
      · have hu' : u - w 0 ∈ Ico 0 (∑ a : Fin (k + 1), w a.succ) := by
          have hh := hu.2
          rw [Fin.sum_univ_succ] at hh
          exact ⟨by linarith only [le_of_not_gt h], by linarith only [hh]⟩
        simp only [h, ite_false, Fin.succ_inj, lower, Fin.cases_succ]
        rw [ih _ (fun a => hw a.succ) _ hu' j]
        simp only [mem_Ico]
        constructor <;> intro hh <;> constructor <;> linarith only [hh.1, hh.2]

theorem measurable_select (k : ℕ) (w : Fin (k + 1) → ℝ) : Measurable (select k w) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    change Measurable (fun u => if u < w 0 then 0 else (select k (fun i => w i.succ) (u - w 0)).succ)
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
      ((measurable_of_countable Fin.succ).comp ((ih _).comp (measurable_id.sub_const _)))

noncomputable def run : (k : ℕ) → (Fin (k + 1) → ℝ) → ℕ → ℝ → PRGRealRAMExecution.Run (Fin (k + 1))
  | 0, _, _, _ => ⟨0, [.control]⟩
  | k + 1, w, address, u =>
    if u < w 0 then ⟨0, [.load address (w 0), .strictComparison u (w 0), .control]⟩
    else
      let difference := PRGRealRAMExecution.arithmetic .sub u (w 0)
      let tail := run k (fun i => w i.succ) (address + 1) difference.value
      ⟨tail.value.succ, [.load address (w 0), .strictComparison u (w 0), .control] ++
        difference.trace ++ tail.trace ++ [.control]⟩

theorem run_data (k : ℕ) (w : Fin (k + 1) → ℝ) (address : ℕ) (u : ℝ) :
    (run k w address u).value = select k w u := by
  induction k generalizing address u with
  | zero => rfl
  | succ k ih =>
    simp only [run, select]
    split_ifs
    · rfl
    · exact congrArg Fin.succ (ih _ _ _)

theorem run_cost (k : ℕ) (w : Fin (k + 1) → ℝ) (address : ℕ) (u : ℝ) :
    (run k w address u).cost ≤ 5 * k + 1 := by
  induction k generalizing address u with
  | zero => exact le_rfl
  | succ k ih =>
    conv => lhs; rw [run]
    split_ifs
    · norm_num [PRGRealRAMExecution.Run.cost, PRGRealRAMExecution.Operation.cost]
      omega
    · have h := ih (fun i => w i.succ) (address + 1) (u - w 0)
      change PRGRealRAMExecution.cost _ ≤ _
      simp only [PRGRealRAMExecution.cost_append, PRGRealRAMExecution.cost_cons, PRGRealRAMExecution.cost_nil,
        PRGRealRAMExecution.Operation.cost, PRGRealRAMExecution.arithmetic]
      change _ + PRGRealRAMExecution.Run.cost (run k (fun i => w i.succ) (address + 1) (u - w 0)) + _ ≤ _
      omega

end Blotto.GeneralPaperRealCumulativeChoice
