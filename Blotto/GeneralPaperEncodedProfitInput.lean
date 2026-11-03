import Blotto.GeneralPaperEncodedProfitField

/-! Owned native weighted-field lists include each field, its weight,
pair descriptor and linked-list cells. Actual weight sums and reached
prefixes discharge every numerator premise without an execution census. -/
namespace Blotto.GeneralPaperEncodedProfitInput
open scoped BigOperators
open GeneralPaperResponseTag GeneralPaperOrderedProfitTreeBuild GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def weightedBits {K : ℕ} (W : ℕ) (f : WeightedField Tag K) : ℕ :=
  GeneralPaperEncodedProfitField.footprint W f.1+natBits f.2+32*W

def footprint {K : ℕ} (W : ℕ) (input : List (WeightedField Tag K)) : ℕ := listFootprint W (weightedBits W) input

def fieldProfile (W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperEncodedProfitField.profile W ((GeneralPaperSourceParameters.prepare k).summarySize+2)
    (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) (lambda+1)

def profile (W m lambda k Qv : ℕ) : ℕ :=
  m*(fieldProfile W m lambda k Qv+GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+34*W)+32*W

theorem weight_word (m lambda k Qv weight : ℕ) (hw : weight≤Qv) :
    natBits weight≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have hc := (GeneralPaperNativeProfitOperands.cap_large
    (GeneralPaperTrajectoryParameters.prepare lambda k).rows Qv (GeneralPaperSourceParameters.prepare k).meshDenominator).2.2.2.2.1
  exact (Nat.add_le_add_left (binaryWordWidth_mono (hw.trans hc)) 1).trans
    (GeneralPaperNativeProfitOperands.operand_word m lambda k Qv)

theorem weight_le {m : ℕ} (weights : FixedArrayTable m ℕ) (Qv : ℕ)
    (hWeights : ∑ j,weights.read j=Qv) (j : Fin m) : weights.read j≤Qv := by
  rw [←hWeights]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

theorem native_field {m k : ℕ} (W Qv : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (hWeights : ∑ j,weights.read j=Qv)
    (hGood : ∀ j,GeneralPaperMeshPrefixInvariant.Good m r.alphabet.lambda k Qv (prefixes.read j))
    (f : WeightedField Tag ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (hf : f∈GeneralPaperOrderedNativeProfitOptimizer.weightedFields k
      (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows weights prefixes r.cached) :
    GeneralPaperEncodedProfitField.footprint W f.1≤fieldProfile W m r.alphabet.lambda k Qv := by
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp hf
  rw [←hj]
  exact GeneralPaperEncodedProfitField.ready W Qv r (weights.read j) (prefixes.read j) j
    (weight_le weights Qv hWeights j) (hGood j)

theorem native_element {m k : ℕ} (W Qv : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (hWeights : ∑ j,weights.read j=Qv)
    (hGood : ∀ j,GeneralPaperMeshPrefixInvariant.Good m r.alphabet.lambda k Qv (prefixes.read j))
    (f : WeightedField Tag ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (hf : f∈GeneralPaperOrderedNativeProfitOptimizer.weightedFields k
      (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows weights prefixes r.cached) :
    weightedBits W f≤fieldProfile W m r.alphabet.lambda k Qv+
      GeneralPaperPowerPreparationEnvelope.operandWidth m r.alphabet.lambda k Qv+32*W := by
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp hf
  rw [←hj]
  have hw := weight_le weights Qv hWeights j
  exact Nat.add_le_add_right (Nat.add_le_add
    (GeneralPaperEncodedProfitField.ready W Qv r (weights.read j) (prefixes.read j) j hw (hGood j))
    (weight_word m r.alphabet.lambda k Qv (weights.read j) hw)) _

theorem native {m k : ℕ} (W Qv : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (hWeights : ∑ j,weights.read j=Qv)
    (hGood : ∀ j,GeneralPaperMeshPrefixInvariant.Good m r.alphabet.lambda k Qv (prefixes.read j)) :
    footprint W (GeneralPaperOrderedNativeProfitOptimizer.weightedFields k
      (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows weights prefixes r.cached)≤profile W m r.alphabet.lambda k Qv := by
  have h := list_bound W (fieldProfile W m r.alphabet.lambda k Qv+
    GeneralPaperPowerPreparationEnvelope.operandWidth m r.alphabet.lambda k Qv+32*W) (weightedBits W) _
    (native_element W Qv r weights prefixes hWeights hGood)
  rw [GeneralPaperOrderedNativeProfitOptimizer.weighted_length] at h
  exact h.trans_eq (by unfold profile; ring)

theorem priced {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W localW Qv : ℕ)
    (r : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (Prefix k)) (hWeights : ∑ j,weights.read j=Qv)
    (hGood : ∀ j,GeneralPaperMeshPrefixInvariant.Good m r.alphabet.lambda k Qv (prefixes.read j)) :
    footprint W (GeneralPaperNativeProfitFieldsExecution.run bits index price localW
      (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows weights prefixes r.cached).1≤profile W m r.alphabet.lambda k Qv := by
  rw [GeneralPaperActualNativeProfitFields.data]
  exact native W Qv r weights prefixes hWeights hGood

end Blotto.GeneralPaperEncodedProfitInput
