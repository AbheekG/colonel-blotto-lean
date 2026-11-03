import Blotto.GeneralPaperNativeRowScore

/-! Physical budget semantics of actual decoded native m-field rows from
bounded closed-threshold catalogues. This joins the real-row resource sum to
the selected shift proof. It does not generate the least-valid code catalogue
or assert any code/payoff correspondence absent that remaining construction.
-/
namespace Blotto.GeneralPaperNativeRowBudget
open scoped BigOperators
open GeneralPaperResponseTag GeneralPaperTagBudgetTransfer
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
open GeneralPaperOrderedNativeProfitOptimizer GeneralPaperNativeRowOptimizer GeneralPaperNativeRowValues
set_option autoImplicit false
set_option maxHeartbeats 3500000

def tags {m K : ℕ} (thresholds : FixedArrayTable m (FixedArrayTable K Farey.Fraction))
    (opened : FixedArrayTable m (FixedArrayTable K Bool)) : FixedArrayTable m (FixedArrayTable K Tag) :=
  FixedArrayTable.ofFn (fun j => FixedArrayTable.ofFn (fun a => ⟨((thresholds.read j).read a).value,(opened.read j).read a⟩))

def physicalRow {m K : ℕ} (thresholds : FixedArrayTable m (FixedArrayTable K Farey.Fraction))
    (opened : FixedArrayTable m (FixedArrayTable K Bool)) (delta : ℚ) (row : FixedArrayTable m (Fin K)) : FixedArrayTable m ℚ :=
  FixedArrayTable.ofFn (fun j => ((thresholds.read j).read (row.read j)).value+if (opened.read j).read (row.read j) then delta else 0)

theorem physical_nonnegative {m K : ℕ} (thresholds : FixedArrayTable m (FixedArrayTable K Farey.Fraction))
    (opened : FixedArrayTable m (FixedArrayTable K Bool)) (delta : ℚ) (hDelta : 0≤delta) (row : FixedArrayTable m (Fin K)) (j : Fin m) :
    0≤(physicalRow thresholds opened delta row).read j := by
  rw [physicalRow,FixedArrayTable.read_ofFn]
  apply add_nonneg (Farey.value_nonnegative _)
  cases (opened.read j).read (row.read j) <;> simp [hDelta]

theorem resource_rowTag {m K : ℕ} (k U T : ℕ) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (summaries : FixedArrayTable m (Summary k)) (codes : FixedArrayTable m (FixedArrayTable K ℕ))
    (thresholds : FixedArrayTable m (FixedArrayTable K Farey.Fraction)) (opened : FixedArrayTable m (FixedArrayTable K Bool))
    (row : FixedArrayTable m (Fin K)) :
    resource k T weights prefixes (plans k U summaries codes (tags thresholds opened)) row=
      rowTag (fun j => (thresholds.read j).read (row.read j)) (fun j => (opened.read j).read (row.read j)) := by
  rw [resource_tags]
  simp only [tags,FixedArrayTable.read_ofFn,rowTag,List.sum_ofFn]

theorem physical_budget_iff {m K : ℕ} (k U T q qbar C : ℕ) (hm : 0<m) (hq : 0<q) (hCap : q≤qbar) (hC : 0<C)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (summaries : FixedArrayTable m (Summary k))
    (codes : FixedArrayTable m (FixedArrayTable K ℕ)) (thresholds : FixedArrayTable m (FixedArrayTable K Farey.Fraction))
    (hDen : ∀ j a, ((thresholds.read j).read a).den≤C) (opened : FixedArrayTable m (FixedArrayTable K Bool))
    (B : ℚ) (hBudgetDen : B.den∣q) (row : FixedArrayTable m (Fin K)) :
    (∑ j, (physicalRow thresholds opened (shift m qbar C) row).read j)≤B ↔
      resource k T weights prefixes (plans k U summaries codes (tags thresholds opened)) row≤budget B := by
  rw [resource_rowTag]
  simp only [physicalRow,FixedArrayTable.read_ofFn]
  exact GeneralPaperTagBudgetTransfer.physical_budget_iff m q qbar C hm hq hCap hC B hBudgetDen
    (fun j => (thresholds.read j).read (row.read j)) (fun j => hDen j (row.read j)) (fun j => (opened.read j).read (row.read j))

theorem budgeted_score_guarantee {m K : ℕ} (lambda k Qv U q qbar C : ℕ) (hm : 0<m) (hq : 0<q) (hCap : q≤qbar) (hC : 0<C)
    (hQv : 0<Qv) (hK : 0<K) (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv)
    (summaries values : FixedArrayTable m (Summary k)) (hTotal : ∀ j, 0<∑ r, (values.read j).read r)
    (codes : FixedArrayTable m (FixedArrayTable K ℕ)) (thresholds : FixedArrayTable m (FixedArrayTable K Farey.Fraction))
    (hDen : ∀ j a, ((thresholds.read j).read a).den≤C) (opened : FixedArrayTable m (FixedArrayTable K Bool))
    (B : ℚ) (hBudgetDen : B.den∣q) (comparator : FixedArrayTable m (Fin K))
    (hBudget : (∑ j, (physicalRow thresholds opened (shift m qbar C) comparator).read j)≤B) :
    ∃ output,
      optimize (GeneralPaperProfitParameters.prepare m lambda k Qv) (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights
        (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes (tags thresholds opened)) B=some output ∧
      (∀ j, 0≤(physicalRow thresholds opened (shift m qbar C) output).read j) ∧
      (∑ j, (physicalRow thresholds opened (shift m qbar C) output).read j)≤B ∧
      score k Qv weights (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes (tags thresholds opened)) comparator-
        score k Qv weights (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes (tags thresholds opened)) output≤
          (GeneralPaperSourceParameters.prepare k).eta/2 := by
  have hSymbolic := (physical_budget_iff k U (GeneralPaperTrajectoryParameters.prepare lambda k).rows q qbar C hm hq hCap hC
    weights (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) summaries codes thresholds hDen opened B hBudgetDen comparator).mp hBudget
  obtain ⟨output,hSolve,hCost,hScore⟩ := GeneralPaperNativeRowScore.score_guarantee lambda k Qv U hQv hK weights hWeights summaries values hTotal codes
    (tags thresholds opened) B comparator hSymbolic
  have hPhysical := (physical_budget_iff k U (GeneralPaperTrajectoryParameters.prepare lambda k).rows q qbar C hm hq hCap hC
    weights (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) summaries codes thresholds hDen opened B hBudgetDen output).mpr hCost
  have hShift := shift_positive m qbar C hm (by omega) hC
  exact ⟨output,hSolve,fun j => physical_nonnegative thresholds opened _ hShift.le output j,hPhysical,hScore⟩

end Blotto.GeneralPaperNativeRowBudget
