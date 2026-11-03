import Blotto.GeneralPaperProfitFieldConstructionStorage

/-! Weighted-field list construction has an invariant for every suffix:
remaining plus completed cells equals the retained field count. Native
callbacks derive all payload bounds; no weight or list-length census runs. -/
namespace Blotto.GeneralPaperProfitListConstructionStorage
open GeneralPaperResponseTag GeneralPaperOrderedProfitTreeBuild GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def Safe {K : ℕ} (W P : ℕ) (xs : List (WeightedField Tag K)) : Prop :=
  ∀ f∈xs,GeneralPaperEncodedProfitInput.weightedBits W f≤P

theorem initial {K : ℕ} (W P m : ℕ) : m+([] : List (WeightedField Tag K)).length=m ∧ Safe W P ([] : List (WeightedField Tag K)) :=
  ⟨by simp,by intro f hf; cases hf⟩

theorem step {K : ℕ} (W P m remaining : ℕ) (xs : List (WeightedField Tag K)) (f : WeightedField Tag K)
    (hn : remaining+1+xs.length=m) (hs : Safe W P xs) (hf : GeneralPaperEncodedProfitInput.weightedBits W f≤P) :
    remaining+(f::xs).length=m ∧ Safe W P (f::xs) := by
  refine ⟨by rw [List.length_cons]; omega,?_⟩
  intro x hx
  rcases List.mem_cons.mp hx with hx|hx
  · subst x; exact hf
  · exact hs x hx

theorem fill_bound {m K : ℕ} (index : ℕ → ℕ) (W A P remaining : ℕ)
    (callback : Fin m → WeightedField Tag K × ℕ) (hb : ∀ j,GeneralPaperEncodedProfitInput.weightedBits W (callback j).1≤P)
    (h : remaining≤m) (xs : List (WeightedField Tag K)) (hn : remaining+xs.length=m) (hs : Safe W P xs) :
    GeneralPaperEncodedProfitInput.footprint W (GeneralPaperIndexedListPrice.fill index A callback remaining h xs).1≤
      m*(P+2*W)+32*W := by
  have hlen : (GeneralPaperIndexedListPrice.fill index A callback remaining h xs).1.length=m := by
    rw [GeneralPaperIndexedListPrice.every_prefix,hn]
  have hpayload := GeneralPaperEncodedScalarStorage.list_bound W P (GeneralPaperEncodedProfitInput.weightedBits W)
    (GeneralPaperIndexedListPrice.fill index A callback remaining h xs).1 (by
      intro f hf
      rw [GeneralPaperIndexedListPrice.fill_data] at hf
      rcases List.mem_append.mp hf with hf|hf
      · obtain ⟨j,hj⟩ := List.mem_ofFn.mp hf
        rw [←hj]
        exact hb _
      · exact hs f hf)
  exact hpayload.trans_eq (by rw [hlen])

theorem native_element {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A Qv : ℕ)
    (r : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (Prefix k)) (hWeights : ∑ j,weights.read j=Qv)
    (hg : ∀ j,GeneralPaperMeshPrefixInvariant.Good m r.alphabet.lambda k Qv (prefixes.read j)) (j : Fin m) :
    GeneralPaperEncodedProfitInput.weightedBits W (GeneralPaperNativeProfitFieldsExecution.element bits index price A
      (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows weights prefixes r.cached j).1≤
      GeneralPaperEncodedProfitInput.fieldProfile W m r.alphabet.lambda k Qv+
        GeneralPaperPowerPreparationEnvelope.operandWidth m r.alphabet.lambda k Qv+32*W := by
  unfold GeneralPaperNativeProfitFieldsExecution.element
  dsimp only
  rw [GeneralPaperNativeProfitLeafExecution.data bits index price A _ (weights.read j) (prefixes.read j)
    (r.cached.read j) (GeneralPaperActualNativeProfitFields.meshes r j)]
  have hw := GeneralPaperEncodedProfitInput.weight_le weights Qv hWeights j
  exact Nat.add_le_add_right (Nat.add_le_add
    (GeneralPaperEncodedProfitField.ready W Qv r (weights.read j) (prefixes.read j) j hw (hg j))
    (GeneralPaperEncodedProfitInput.weight_word m r.alphabet.lambda k Qv (weights.read j) hw)) _

theorem native_fill {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A Qv remaining : ℕ)
    (r : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (Prefix k)) (hWeights : ∑ j,weights.read j=Qv)
    (hg : ∀ j,GeneralPaperMeshPrefixInvariant.Good m r.alphabet.lambda k Qv (prefixes.read j)) (h : remaining≤m)
    (xs : List (WeightedField Tag ((GeneralPaperSourceParameters.prepare k).summarySize+2))) (hn : remaining+xs.length=m)
    (hs : Safe W (GeneralPaperEncodedProfitInput.fieldProfile W m r.alphabet.lambda k Qv+
      GeneralPaperPowerPreparationEnvelope.operandWidth m r.alphabet.lambda k Qv+32*W) xs) :
    GeneralPaperEncodedProfitInput.footprint W (GeneralPaperIndexedListPrice.fill index
      (if bits then GeneralPaperSummaryArrayExecution.arrayWord A (m+2) else A)
      (GeneralPaperNativeProfitFieldsExecution.element bits index price A
        (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows weights prefixes r.cached) remaining h xs).1≤
      GeneralPaperEncodedProfitInput.profile W m r.alphabet.lambda k Qv := by
  have hb := fill_bound index W (if bits then GeneralPaperSummaryArrayExecution.arrayWord A (m+2) else A)
    (GeneralPaperEncodedProfitInput.fieldProfile W m r.alphabet.lambda k Qv+
      GeneralPaperPowerPreparationEnvelope.operandWidth m r.alphabet.lambda k Qv+32*W) remaining
    (GeneralPaperNativeProfitFieldsExecution.element bits index price A
      (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows weights prefixes r.cached)
    (native_element bits index price W A Qv r weights prefixes hWeights hg) h xs hn hs
  exact hb.trans_eq (by unfold GeneralPaperEncodedProfitInput.profile; ring)

end Blotto.GeneralPaperProfitListConstructionStorage
