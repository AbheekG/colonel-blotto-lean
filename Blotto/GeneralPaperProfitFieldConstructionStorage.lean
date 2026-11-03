import Blotto.GeneralPaperRootSelectionStorage

/-! Actual profit-field fill prefixes include all reserved slots. The
retained coefficient, returned tail-count record and current output pair
have source-derived words. Internal quotient/comparison scratch remains
separate; this introduces no query, weight or encoding calibration pass. -/
namespace Blotto.GeneralPaperProfitFieldConstructionStorage
open GeneralPaperResponseTag GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def optionCap (W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+(1+2*(lambda+1))+1+24*W

theorem element_bound {m k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W A Qv : ℕ)
    (r : GeneralPaperCatalogueOptimizer.Ready m k) (weight : ℕ) (prefixes : Prefix k) (j : Fin m)
    (hw : weight≤Qv) (hg : GeneralPaperMeshPrefixInvariant.Good m r.alphabet.lambda k Qv prefixes)
    (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    GeneralPaperEncodedProfitField.optionBits W (GeneralPaperNativeProfitLeafExecution.element bits price A
      (2*(GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows*weight) prefixes (r.cached.read j) i).1≤
      optionCap W m r.alphabet.lambda k Qv := by
  rw [GeneralPaperNativeProfitLeafExecution.element_data bits price A _ prefixes (r.cached.read j) i
    (GeneralPaperActualNativeProfitFields.meshes r j)]
  have hn := GeneralPaperEncodedProfitField.numerator_word m r.alphabet.lambda Qv weight prefixes
    (r.cached.read j) hw (GeneralPaperActualNativeProfitFields.meshes r j) hg i
  rw [GeneralPaperOrderedNativeOptionProfits.read_build] at hn
  have ht := rationalWordWidth_of_height (GeneralPaperTagHeight.ready_height r j i)
  unfold GeneralPaperEncodedProfitField.optionBits optionCap
  dsimp only at hn ⊢
  omega

def prefixFootprint {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A : ℕ)
    (r : GeneralPaperCatalogueOptimizer.Ready m k) (weight : ℕ) (prefixes : Prefix k) (j : Fin m)
    (count : ℕ) (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) : ℕ :=
  let primitive := if bits then price else fun _ => 1
  let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
  let coefficient := GeneralPaperNativeProfitScalarPrice.coefficient primitive A
    (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows weight
  GeneralPaperEncodedReferenceVector.reservedFootprint W K (GeneralPaperEncodedProfitField.optionBits W)
    (PaperIndexedArrayConstruction.fill index (if bits then GeneralPaperSummaryArrayExecution.arrayWord A K else A)
      (GeneralPaperNativeProfitLeafExecution.element bits primitive A coefficient.1 prefixes (r.cached.read j)) count hc).1

def prefixProfile (W m lambda k Qv : ℕ) : ℕ :=
  ((GeneralPaperSourceParameters.prepare k).summarySize+2)*(optionCap W m lambda k Qv+W)+64*W

theorem prefix_bound {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A Qv : ℕ)
    (r : GeneralPaperCatalogueOptimizer.Ready m k) (weight : ℕ) (prefixes : Prefix k) (j : Fin m)
    (hw : weight≤Qv) (hg : GeneralPaperMeshPrefixInvariant.Good m r.alphabet.lambda k Qv prefixes)
    (count : ℕ) (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) :
    prefixFootprint bits index price W A r weight prefixes j count hc≤prefixProfile W m r.alphabet.lambda k Qv := by
  unfold prefixFootprint
  dsimp only
  apply GeneralPaperEncodedReferenceVector.indexed_reserved_prefix
  intro i
  exact element_bound bits (if bits then price else fun _ => 1) W A Qv r weight prefixes j hw hg i

theorem coefficient_word {m k : ℕ} (price : ℕ → ℕ) (A Qv : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (weight : ℕ) (hw : weight≤Qv) :
    natBits (GeneralPaperNativeProfitScalarPrice.coefficient price A
      (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows weight).1≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m r.alphabet.lambda k Qv := by
  have hc := (GeneralPaperNativeProfitOperands.coefficient_bound
    (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows Qv
    (GeneralPaperSourceParameters.prepare k).meshDenominator weight hw).2
  exact (Nat.add_le_add_left (binaryWordWidth_mono hc) 1).trans
    (GeneralPaperNativeProfitOperands.operand_word m r.alphabet.lambda k Qv)

def pairFootprint (W : ℕ) (p : GeneralPaperSignedTailPlan.Pair) : ℕ := fields W [p.positive,p.negative,p.work]+64*W

theorem pair_bound {m k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W A Qv : ℕ)
    (r : GeneralPaperCatalogueOptimizer.Ready m k) (prefixes : Prefix k) (j : Fin m)
    (hg : GeneralPaperMeshPrefixInvariant.Good m r.alphabet.lambda k Qv prefixes)
    (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    pairFootprint W (GeneralPaperMeshPairExecution.tails bits price A (r.cached.read j).mesh prefixes (r.cached.read j).tails i).1≤
      3*(GeneralPaperPowerPreparationEnvelope.operandWidth m r.alphabet.lambda k Qv+W)+96*W := by
  let p := (GeneralPaperMeshPairExecution.tails bits price A (r.cached.read j).mesh prefixes (r.cached.read j).tails i).1
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m r.alphabet.lambda k Qv
  let T := (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows
  let mesh := (r.cached.read j).mesh
  have hm := GeneralPaperActualNativeProfitFields.meshes r j
  have hp := GeneralPaperMeshCountBounds.cached_interval_bound bits price A m r.alphabet.lambda Qv mesh prefixes
    (r.cached.read j).tails.positive i.castSucc (Fin.last _) hm hg
  have hn := GeneralPaperMeshCountBounds.cached_interval_bound bits price A m r.alphabet.lambda Qv mesh prefixes
    (r.cached.read j).tails.negative i.castSucc (Fin.last _) hm hg
  change p.positive≤mesh at hp
  change p.negative≤mesh at hn
  have hcap := (GeneralPaperNativeProfitOperands.cap_large T Qv mesh).2.2.2.1
  have hmesh : mesh≤GeneralPaperNativeProfitOperands.cap T Qv mesh := by omega
  have hword : natBits (GeneralPaperNativeProfitOperands.cap T Qv mesh)≤H := by
    dsimp only [mesh,T,H]
    rw [hm]
    exact GeneralPaperNativeProfitOperands.operand_word m r.alphabet.lambda k Qv
  have hpw := (Nat.add_le_add_left (binaryWordWidth_mono (hp.trans hmesh)) 1).trans hword
  have hnw := (Nat.add_le_add_left (binaryWordWidth_mono (hn.trans hmesh)) 1).trans hword
  have hwork : p.work=24*(30+k)+124 := by
    dsimp only [p]
    rw [GeneralPaperMeshPairExecution.tails_data bits price A _ _ _ _ hm,GeneralPaperSignedTailPlan.evaluate_work]
  have hworkcap : p.work≤GeneralPaperMeshQueryMetadata.cap k := by rw [hwork]; unfold GeneralPaperMeshQueryMetadata.cap; omega
  have hww := (Nat.add_le_add_left (binaryWordWidth_mono hworkcap) 1).trans
    (GeneralPaperMeshQueryMetadata.operand_word m r.alphabet.lambda k Qv)
  have hf := fields_bound W H [p.positive,p.negative,p.work] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact hpw
    · exact hnw
    · exact hww)
  change _≤3*(H+W)+32*W at hf
  exact (Nat.add_le_add_right hf (64*W)).trans_eq (by ring)

end Blotto.GeneralPaperProfitFieldConstructionStorage
