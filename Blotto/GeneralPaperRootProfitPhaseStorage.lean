import Blotto.GeneralPaperZeroPaddingStorage

/-! Root scan, one live profit-field fill/query record, completed field
suffix, full input owner and shared zero-padding buffers have one native
phase-window bound. Exact root and literal budget words stay explicit;
internal query/primitive scratch remains separate. -/
namespace Blotto.GeneralPaperRootProfitPhaseStorage
open GeneralPaperResponseTag
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperEncodedScalarStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem completed_suffix {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A Qv remaining : ℕ)
    (r : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (Prefix k)) (hWeights : ∑ j,weights.read j=Qv)
    (hg : ∀ j,GeneralPaperMeshPrefixInvariant.Good m r.alphabet.lambda k Qv (prefixes.read j)) :
    GeneralPaperEncodedProfitInput.footprint W ((GeneralPaperNativeProfitFieldsExecution.run bits index price A
      (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows weights prefixes r.cached).1.drop remaining)≤
      GeneralPaperEncodedProfitInput.profile W m r.alphabet.lambda k Qv := by
  let input := (GeneralPaperNativeProfitFieldsExecution.run bits index price A
    (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows weights prefixes r.cached).1
  let P := GeneralPaperEncodedProfitInput.fieldProfile W m r.alphabet.lambda k Qv+
    GeneralPaperPowerPreparationEnvelope.operandWidth m r.alphabet.lambda k Qv+32*W
  have hp := list_bound W P (GeneralPaperEncodedProfitInput.weightedBits W) (input.drop remaining) (by
    intro f hf
    have hi := List.mem_of_mem_drop hf
    change f∈(GeneralPaperNativeProfitFieldsExecution.run bits index price A
      (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows weights prefixes r.cached).1 at hi
    rw [GeneralPaperActualNativeProfitFields.data] at hi
    exact GeneralPaperEncodedProfitInput.native_element W Qv r weights prefixes hWeights hg f hi)
  have hn : (input.drop remaining).length≤m := by
    rw [List.length_drop]
    have hi : input.length=m := GeneralPaperNativeProfitFieldsExecution.length bits index price A _ weights prefixes r.cached
    rw [hi]
    exact Nat.sub_le _ _
  have hlength := Nat.add_le_add_right (Nat.mul_le_mul_right (P+2*W) hn) (32*W)
  exact hp.trans (hlength.trans_eq (by unfold P GeneralPaperEncodedProfitInput.profile; ring))

def window {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (B : ℚ)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (count copied : ℕ) (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) : ℕ :=
  let primitive := if bits then price else fun _ => 1
  let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
  let plan := r.cached.read j
  let tree := GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared T weights prefixes r.cached
  let input := (GeneralPaperNativeProfitFieldsExecution.run bits index price A T weights prefixes r.cached).1
  let zeroA := if bits then GeneralPaperSummaryArrayExecution.arrayWord A K else A
  let padA := if bits then GeneralPaperSummaryArrayExecution.arrayWord A (prepared.parameters.leafCount+2) else A
  GeneralPaperRootSelectionStorage.window bits index primitive W A (GeneralPaperOrderedProfitDP.run prepared.grid tree).table (budget B)+
    GeneralPaperProfitFieldConstructionStorage.prefixFootprint bits index price W A r (weights.read j) (prefixes.read j) j count hc+
    natBits (GeneralPaperNativeProfitScalarPrice.coefficient primitive A T (weights.read j)).1+
    GeneralPaperProfitFieldConstructionStorage.pairFootprint W
      (GeneralPaperMeshPairExecution.tails bits primitive A plan.mesh (prefixes.read j) plan.tails i).1+
    GeneralPaperEncodedProfitField.optionBits W (GeneralPaperNativeProfitLeafExecution.element bits primitive A
      (2*T*weights.read j) (prefixes.read j) plan i).1+
    GeneralPaperEncodedProfitInput.footprint W (input.drop (j.val+1))+GeneralPaperEncodedProfitInput.footprint W input+
    GeneralPaperEncodedReferenceVector.reservedFootprint W K (GeneralPaperEncodedProfitField.optionBits W)
      (PaperIndexedArrayConstruction.fill index zeroA (fun _ : Fin K => (((0,(0:Tag)),64*zeroA))) count hc).1+
    GeneralPaperZeroPaddingStorage.appendWindow W input
      (GeneralPaperIndexedListPrice.run index padA
        (fun _ : Fin (prepared.parameters.leafCount-m) => (GeneralPaperOrderedProfitTreeBuild.dummy Tag K,64*W))).1 copied+2+160*W

def profile (W m lambda k Qv : ℕ) (prepared : GeneralPaperProfitParameters.Prepared) (budgetWord : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
  GeneralPaperRootSelectionStorage.profile W prepared.grid.size
      (expressionHeightBudget (lambda+1) prepared.parameters.height) budgetWord+
    GeneralPaperProfitFieldConstructionStorage.prefixProfile W m lambda k Qv+H+(3*(H+W)+96*W)+
    GeneralPaperProfitFieldConstructionStorage.optionCap W m lambda k Qv+
    2*GeneralPaperEncodedProfitInput.profile W m lambda k Qv+
    (K*(2+(1+2*(lambda+1))+1+25*W)+64*W)+(72*prepared.parameters.leafCount*W+256*W)+2+160*W

theorem ready {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A Qv : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (B : ℚ)
    (hT : T=(GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows)
    (hPrepared : prepared=GeneralPaperProfitParameters.prepare m r.alphabet.lambda k Qv)
    (hWeights : ∑ j,weights.read j=Qv)
    (hg : ∀ j,GeneralPaperMeshPrefixInvariant.Good m r.alphabet.lambda k Qv (prefixes.read j))
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (count copied : ℕ) (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) :
    window bits index price W A prepared T r weights prefixes B j i count copied hc≤
      profile W m r.alphabet.lambda k Qv prepared (rationalWordWidth B) := by
  subst T
  let primitive := if bits then price else fun _ => 1
  let T := (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows
  let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
  let input := (GeneralPaperNativeProfitFieldsExecution.run bits index price A T weights prefixes r.cached).1
  let tree := GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared T weights prefixes r.cached
  let zeroA := if bits then GeneralPaperSummaryArrayExecution.arrayWord A K else A
  let padA := if bits then GeneralPaperSummaryArrayExecution.arrayWord A (prepared.parameters.leafCount+2) else A
  have hw := GeneralPaperEncodedProfitInput.weight_le weights Qv hWeights j
  have hroot := GeneralPaperRootSelectionStorage.native bits index primitive W A
    (expressionHeightBudget (r.alphabet.lambda+1) prepared.parameters.height)
    (GeneralPaperOrderedProfitDP.run prepared.grid tree).table (budget B)
    (GeneralPaperOrderedDPHeight.native_states prepared T r weights prefixes)
  have hprefix := GeneralPaperProfitFieldConstructionStorage.prefix_bound bits index price W A Qv r (weights.read j) (prefixes.read j) j hw (hg j) count hc
  have hcoeff := GeneralPaperProfitFieldConstructionStorage.coefficient_word primitive A Qv r (weights.read j) hw
  have hpair := GeneralPaperProfitFieldConstructionStorage.pair_bound bits primitive W A Qv r (prefixes.read j) j (hg j) i
  have helem := GeneralPaperProfitFieldConstructionStorage.element_bound bits primitive W A Qv r (weights.read j) (prefixes.read j) j hw (hg j) i
  have hsuffix := completed_suffix bits index price W A Qv (j.val+1) r weights prefixes hWeights hg
  have hinput := GeneralPaperEncodedProfitInput.priced bits index price W A Qv r weights prefixes hWeights hg
  have hzero := GeneralPaperZeroPaddingStorage.zero_prefix index W zeroA K (r.alphabet.lambda+1) count (by omega) hc
  have hfit : m≤prepared.parameters.leafCount := by
    rw [hPrepared]
    exact GeneralPaperProfitParameters.covers_fields m r.alphabet.lambda k Qv
  have hpadding := GeneralPaperZeroPaddingStorage.native_padding index W padA prepared.parameters.leafCount m copied
    (GeneralPaperOrderedProfitTreeBuild.dummy Tag K) input
    (GeneralPaperNativeProfitFieldsExecution.length bits index price A T weights prefixes r.cached) hfit
  have total := Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add hroot hprefix) hcoeff) hpair) helem) hsuffix) hinput) hzero) hpadding) 2) (160*W)
  exact total.trans_eq (by
    unfold profile
    dsimp only
    dsimp only [K,GeneralPaperResponseTag.budget]
    ring)

end Blotto.GeneralPaperRootProfitPhaseStorage
