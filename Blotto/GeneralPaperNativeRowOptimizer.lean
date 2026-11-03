import Blotto.GeneralPaperOrderedRowOptimizer

/-! Native actual-profit optimizer returning exactly m option indices.
The prepared grid and cached plans are inputs. Positive current value arrays
and the rounded-value sum derive the profit domain, and every feasible real
m-field row is a comparator; no padded tree witness is supplied.
-/
namespace Blotto.GeneralPaperNativeRowOptimizer
open scoped BigOperators
open GeneralPaperResponseTag
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
open GeneralPaperOrderedProfitRows GeneralPaperOrderedProfitTreeBuild
open GeneralPaperOrderedNativeProfitOptimizer
set_option autoImplicit false
set_option maxHeartbeats 3500000

def resource {m K : ℕ} (k T : ℕ) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (cached : FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan Tag k K)) (row : FixedArrayTable m (Fin K)) : Tag :=
  (resources ((weightedFields k T weights prefixes cached).map Prod.fst) (List.ofFn row.read)).sum

def trueProfit {m K : ℕ} (k T : ℕ) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (cached : FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan Tag k K)) (row : FixedArrayTable m (Fin K)) : ℕ :=
  (profits ((weightedFields k T weights prefixes cached).map Prod.fst) (List.ofFn row.read)).sum

def optimize {m K k : ℕ} (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (Prefix k)) (cached : FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan Tag k K)) (B : ℚ) :
    Option (FixedArrayTable m (Fin K)) :=
  (GeneralPaperOrderedRowOptimizer.optimize prepared (weightedFields k T weights prefixes cached) (budget B)).map
    (GeneralPaperRowPrefix.resize (weighted_length k T weights prefixes cached))

theorem native_guarantee {m K : ℕ} (lambda k Qv U : ℕ) (hQv : 0<Qv) (hK : 0<K) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (summaries values : FixedArrayTable m (Summary k))
    (hTotal : ∀ j, 0<∑ r, (values.read j).read r) (codes : FixedArrayTable m (FixedArrayTable K ℕ))
    (tags : FixedArrayTable m (FixedArrayTable K Tag)) (B : ℚ) (comparator : FixedArrayTable m (Fin K))
    (hBudget : resource k (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights
      (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes tags) comparator≤budget B) :
    ∃ output,
      optimize (GeneralPaperProfitParameters.prepare m lambda k Qv) (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights
        (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes tags) B=some output ∧
      (resource k (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights
        (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes tags) output≤budget B) ∧
      GeneralPaperProfitRationalRound.profit (GeneralPaperProfitParameters.parameters m lambda k Qv).qProf
          (trueProfit k (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights
            (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes tags) comparator)-
        GeneralPaperProfitRationalRound.profit (GeneralPaperProfitParameters.parameters m lambda k Qv).qProf
          (trueProfit k (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights
            (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes tags) output)≤
        (GeneralPaperSourceParameters.prepare k).eta/2 := by
  let prefixes : FixedArrayTable m (Prefix k) := FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))
  let cached := plans k U summaries codes tags
  let input := weightedFields k (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights prefixes cached
  have hLength : input.length=m := weighted_length k _ weights prefixes cached
  have hFit : input.length≤2^(GeneralPaperProfitParameters.parameters m lambda k Qv).height := by
    rw [hLength]
    have he := GeneralPaperProfitParameters.covers_fields m lambda k Qv
    rw [GeneralPaperProfitParameters.leaf_count_spec] at he
    exact he
  have hc := padded_capacity (2*(GeneralPaperTrajectoryParameters.prepare lambda k).rows*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (GeneralPaperProfitParameters.parameters m lambda k Qv).height input hFit
    (native_capacities k U (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights summaries values hTotal codes tags)
  have hs : (input.map Prod.snd).sum=Qv := (weight_sum k _ weights prefixes cached).trans hWeights
  rw [hs] at hc
  have hb := GeneralPaperOrderedProfitCapacity.source_bounded m lambda k Qv _ hc
  let comp := GeneralPaperRowPrefix.resize hLength.symm comparator
  have hCompCost : GeneralPaperOrderedRowOptimizer.resource input comp=
      resource k (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights prefixes cached comparator := by
    dsimp only [GeneralPaperOrderedRowOptimizer.resource,resource,comp]
    rw [GeneralPaperRowPrefix.resize_ofFn]
  have hCompProfit : GeneralPaperOrderedRowOptimizer.trueProfit input comp=
      trueProfit k (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights prefixes cached comparator := by
    dsimp only [GeneralPaperOrderedRowOptimizer.trueProfit,trueProfit,comp]
    rw [GeneralPaperRowPrefix.resize_ofFn]
  obtain ⟨out,hSolve,hCost,hProfit⟩ := GeneralPaperOrderedRowOptimizer.selected_guarantee m lambda k Qv hQv hK input hLength.le (budget B) hb comp
    (by rw [hCompCost]; exact hBudget)
  let output := GeneralPaperRowPrefix.resize hLength out
  have hOutCost : resource k (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights prefixes cached output=
      GeneralPaperOrderedRowOptimizer.resource input out := by
    dsimp only [resource,GeneralPaperOrderedRowOptimizer.resource,output]
    rw [GeneralPaperRowPrefix.resize_ofFn]
  have hOutProfit : trueProfit k (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights prefixes cached output=
      GeneralPaperOrderedRowOptimizer.trueProfit input out := by
    dsimp only [trueProfit,GeneralPaperOrderedRowOptimizer.trueProfit,output]
    rw [GeneralPaperRowPrefix.resize_ofFn]
  refine ⟨output,?_,?_,?_⟩
  · change (GeneralPaperOrderedRowOptimizer.optimize _ input (budget B)).map _=some output
    rw [hSolve]
    rfl
  · change resource k (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights prefixes cached output≤budget B
    rw [hOutCost]
    exact hCost
  · change GeneralPaperProfitRationalRound.profit _ (trueProfit k _ weights prefixes cached comparator)-
        GeneralPaperProfitRationalRound.profit _ (trueProfit k _ weights prefixes cached output)≤_
    rw [←hCompProfit,hOutProfit]
    exact hProfit

end Blotto.GeneralPaperNativeRowOptimizer
