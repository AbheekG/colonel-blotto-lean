import Blotto.GeneralPaperNativeRowOptimizer

/-! Exact values of the real native row. Tags are the original catalogue
tags, with no contribution from dummy fields. True integer input profits
normalize to the selected weighted rounded signed-tail objective.
-/
namespace Blotto.GeneralPaperNativeRowValues
open scoped BigOperators
open GeneralPaperResponseTag
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
open GeneralPaperOrderedNativeProfitOptimizer GeneralPaperNativeRowOptimizer
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem zip_ofFn {α β : Type*} {m : ℕ} (f : Fin m → α) (g : Fin m → β) :
    (List.ofFn f).zip (List.ofFn g)=List.ofFn (fun j => (f j,g j)) := by
  apply List.ext_getElem <;> simp

theorem resource_sum {m K : ℕ} (k T : ℕ) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (cached : FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan Tag k K)) (row : FixedArrayTable m (Fin K)) :
    resource k T weights prefixes cached row=∑ j, (cached.read j).tags.read (row.read j) := by
  dsimp only [resource,GeneralPaperOrderedProfitRows.resources,weightedFields]
  simp only [List.map_ofFn,Function.comp_def,zip_ofFn,GeneralPaperOrderedNativeOptionProfits.tag_preserved,List.sum_ofFn]

theorem resource_tags {m K : ℕ} (k U T : ℕ) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (summaries : FixedArrayTable m (Summary k)) (codes : FixedArrayTable m (FixedArrayTable K ℕ))
    (tags : FixedArrayTable m (FixedArrayTable K Tag)) (row : FixedArrayTable m (Fin K)) :
    resource k T weights prefixes (plans k U summaries codes tags) row=∑ j, (tags.read j).read (row.read j) := by
  rw [resource_sum]
  simp only [plans,FixedArrayTable.read_ofFn,GeneralPaperOrderedNativeOptionProfits.prepare]

theorem profit_sum {m K : ℕ} (k T : ℕ) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (cached : FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan Tag k K)) (row : FixedArrayTable m (Fin K)) :
    trueProfit k T weights prefixes cached row=
      ∑ j, ((GeneralPaperOrderedNativeOptionProfits.build k T (weights.read j) (prefixes.read j) (cached.read j)).1.read (row.read j)).1 := by
  dsimp only [trueProfit,GeneralPaperOrderedProfitRows.profits,weightedFields]
  simp only [List.map_ofFn,Function.comp_def,zip_ofFn,List.sum_ofFn]

def score {m K : ℕ} (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (cached : FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan Tag k K)) (row : FixedArrayTable m (Fin K)) : ℚ :=
  ∑ j, (weights.read j:ℚ)/Qv*GeneralPaperSignedTailValues.value k
    (GeneralPaperSignedTailPlan.evaluate k (prefixes.read j) (cached.read j).tails (row.read j))

theorem normalized_profit {m K : ℕ} (lambda k Qv U : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (summaries values : FixedArrayTable m (Summary k)) (hTotal : ∀ j, 0<∑ r, (values.read j).read r)
    (codes : FixedArrayTable m (FixedArrayTable K ℕ)) (tags : FixedArrayTable m (FixedArrayTable K Tag))
    (row : FixedArrayTable m (Fin K)) :
    GeneralPaperProfitRationalRound.profit (GeneralPaperProfitParameters.parameters m lambda k Qv).qProf
      (trueProfit k (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights
        (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes tags) row)=
      (∑ j, (weights.read j:ℚ)/Qv)+score k Qv weights
        (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes tags) row := by
  rw [profit_sum]
  unfold GeneralPaperProfitRationalRound.profit
  rw [Nat.cast_sum,Finset.sum_div]
  have he : ∀ j : Fin m,
      ((((GeneralPaperOrderedNativeOptionProfits.build k (GeneralPaperTrajectoryParameters.prepare lambda k).rows (weights.read j)
        (GeneralPaperEpochPrefixArray.build (values.read j))
        (GeneralPaperOrderedNativeOptionProfits.prepare k U (summaries.read j) (codes.read j) (tags.read j))).1.read (row.read j)).1:ℕ):ℚ)/
        (GeneralPaperProfitParameters.parameters m lambda k Qv).qProf=
      (weights.read j:ℚ)/Qv*(1+GeneralPaperSignedTailValues.value k
        (GeneralPaperSignedTailPlan.evaluate k (GeneralPaperEpochPrefixArray.build (values.read j))
          (GeneralPaperSignedTailPlan.prepare k U (summaries.read j) (codes.read j)) (row.read j))) := by
    intro j
    exact GeneralPaperOrderedNativeOptionProfits.normalized_value m lambda k Qv U (weights.read j) hQv
      (summaries.read j) (values.read j) (hTotal j) (codes.read j) (tags.read j) (row.read j)
  simp only [plans,FixedArrayTable.read_ofFn]
  simp only [he,mul_add,mul_one,Finset.sum_add_distrib]
  simp only [score,plans,FixedArrayTable.read_ofFn,GeneralPaperOrderedNativeOptionProfits.prepare]

end Blotto.GeneralPaperNativeRowValues
