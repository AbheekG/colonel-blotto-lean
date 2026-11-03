import Blotto.GeneralPaperOrderedProfitTreeBuild

/-! Join cached signed-tail plans, actual current prefix arrays, native
nonnegative option profits, balanced dummy padding and the prepared optimizer.
The profit-domain bound is derived from the rounded-value weight sum. The
physical code/tag catalogue, whole-row decoding and full prices remain joins.
-/
namespace Blotto.GeneralPaperOrderedNativeProfitOptimizer
open scoped BigOperators
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
open GeneralPaperOrderedProfitDP GeneralPaperOrderedProfitSound GeneralPaperOrderedProfitTreeBuild
set_option autoImplicit false
variable {R : Type} [LinearOrder R] [AddCommMonoid R] [IsOrderedAddMonoid R]
set_option maxHeartbeats 3500000

def plans {m K : ℕ} (k U : ℕ) (summaries : FixedArrayTable m (Summary k))
    (codes : FixedArrayTable m (FixedArrayTable K ℕ)) (tags : FixedArrayTable m (FixedArrayTable K R)) :
    FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan R k K) :=
  FixedArrayTable.ofFn (fun j => GeneralPaperOrderedNativeOptionProfits.prepare k U (summaries.read j) (codes.read j) (tags.read j))

def weightedFields {m K : ℕ} (k T : ℕ) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (preparedPlans : FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan R k K)) : List (WeightedField R K) :=
  List.ofFn (fun j => ((GeneralPaperOrderedNativeOptionProfits.build k T (weights.read j) (prefixes.read j) (preparedPlans.read j)).1,weights.read j))

def inputTree {m K k : ℕ} (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (Prefix k)) (preparedPlans : FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan R k K)) :
    Tree R K prepared.parameters.height :=
  GeneralPaperOrderedProfitTreeBuild.build prepared.parameters.height
    (pad prepared.parameters.height (weightedFields k T weights prefixes preparedPlans))

def optimize {m K k : ℕ} (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (Prefix k)) (preparedPlans : FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan R k K)) (budget : R) :
    Option (Fin prepared.grid.size × List (Fin K)) :=
  GeneralPaperOrderedProfitRoot.solve prepared.grid (inputTree prepared T weights prefixes preparedPlans) budget

theorem weighted_length {m K : ℕ} (k T : ℕ) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (preparedPlans : FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan R k K)) :
    (weightedFields k T weights prefixes preparedPlans).length=m := List.length_ofFn

theorem weight_sum {m K : ℕ} (k T : ℕ) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (preparedPlans : FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan R k K)) :
    ((weightedFields k T weights prefixes preparedPlans).map Prod.snd).sum=∑ j, weights.read j := by
  simp only [weightedFields,List.map_ofFn,Function.comp_def,List.sum_ofFn]

theorem native_capacities {m K : ℕ} (k U T : ℕ) (weights : FixedArrayTable m ℕ)
    (summaries values : FixedArrayTable m (Summary k)) (hTotal : ∀ j, 0<∑ r, (values.read j).read r)
    (codes : FixedArrayTable m (FixedArrayTable K ℕ)) (tags : FixedArrayTable m (FixedArrayTable K R)) :
    ∀ field∈weightedFields k T weights (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes tags),
      GeneralPaperOrderedProfitCapacity.Capacity (2*T*(GeneralPaperSourceParameters.prepare k).meshDenominator) (.leaf field.1) field.2 := by
  intro field hField
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hField
  simp only [plans,FixedArrayTable.read_ofFn]
  exact GeneralPaperOrderedProfitCapacity.native_leaf k U T (weights.read j) (summaries.read j) (values.read j) (hTotal j) (codes.read j) (tags.read j)

theorem native_guarantee {m K : ℕ} (lambda k Qv U : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (summaries values : FixedArrayTable m (Summary k))
    (hTotal : ∀ j, 0<∑ r, (values.read j).read r) (codes : FixedArrayTable m (FixedArrayTable K ℕ)) (tags : FixedArrayTable m (FixedArrayTable K R))
    (budget : R) (labels : List (Fin K)) (cost : R) (P : ℕ)
    (hRealizes : Realizes (inputTree (GeneralPaperProfitParameters.prepare m lambda k Qv) (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights
      (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes tags)) labels cost P)
    (hBudget : cost≤budget) :
    ∃ label output outCost outProfit,
      optimize (GeneralPaperProfitParameters.prepare m lambda k Qv) (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights
        (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes tags) budget=some (label,output) ∧
      Realizes (inputTree (GeneralPaperProfitParameters.prepare m lambda k Qv) (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights
        (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (plans k U summaries codes tags)) output outCost outProfit ∧
      outCost≤budget ∧ GeneralPaperProfitRationalRound.profit (GeneralPaperProfitParameters.parameters m lambda k Qv).qProf P-
        GeneralPaperProfitRationalRound.profit (GeneralPaperProfitParameters.parameters m lambda k Qv).qProf outProfit≤(GeneralPaperSourceParameters.prepare k).eta/2 := by
  let prefixes : FixedArrayTable m (Prefix k) := FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))
  let cached := plans k U summaries codes tags
  let input := weightedFields k (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights prefixes cached
  have hLen : input.length≤2^(GeneralPaperProfitParameters.parameters m lambda k Qv).height := by
    rw [weighted_length]
    have he := GeneralPaperProfitParameters.covers_fields m lambda k Qv
    rw [GeneralPaperProfitParameters.leaf_count_spec] at he
    exact he
  have hc := padded_capacity (2*(GeneralPaperTrajectoryParameters.prepare lambda k).rows*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (GeneralPaperProfitParameters.parameters m lambda k Qv).height input hLen
    (native_capacities k U (GeneralPaperTrajectoryParameters.prepare lambda k).rows weights summaries values hTotal codes tags)
  have hs : (input.map Prod.snd).sum=Qv := (weight_sum k _ weights prefixes cached).trans hWeights
  rw [hs] at hc
  have hb := GeneralPaperOrderedProfitCapacity.source_bounded m lambda k Qv _ hc
  exact GeneralPaperOrderedSelectedProfitGuarantee.selected_guarantee m lambda k Qv hQv _ budget hb labels cost P hRealizes hBudget

end Blotto.GeneralPaperOrderedNativeProfitOptimizer
