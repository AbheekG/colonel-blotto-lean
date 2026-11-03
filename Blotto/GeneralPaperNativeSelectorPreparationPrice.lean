import Blotto.GeneralPaperNativeSelectorExecution

/-! Join the existing native input and tree prices without repeating either
construction. Source records supply the retained span and field count. -/
namespace Blotto.GeneralPaperNativeSelectorPreparationPrice
open GeneralPaperUnsignedCellConstancy (Prefix)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem span (m lambda k Qv : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (hp : prepared=GeneralPaperProfitParameters.prepare m lambda k Qv) :
    prepared.parameters.leafCount=2^prepared.parameters.height ∧ m≤prepared.parameters.leafCount := by
  subst prepared
  exact ⟨GeneralPaperProfitParameters.leaf_count_spec m lambda k Qv,GeneralPaperProfitParameters.covers_fields m lambda k Qv⟩

def profile (model : RationalCostModel) (W m lambda k Qv K height leaves : ℕ) : ℕ :=
  GeneralPaperNativeProfitFieldsPrice.profile model.rat W m lambda k Qv K+
    GeneralPaperProfitTreePreparation.bitProfile model.rat W m K height leaves+128*W

def arithmeticProfile (m k K height leaves : ℕ) : ℕ :=
  GeneralPaperNativeProfitFieldsPrice.arithmeticProfile m K k+
    GeneralPaperProfitTreePreparation.arithmeticProfile m K height leaves+128

theorem work {m k : ℕ} (model : RationalCostModel) (W lambda Qv T : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (hp : prepared=GeneralPaperProfitParameters.prepare m lambda k Qv)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (hT : T=(GeneralPaperTrajectoryParameters.prepare lambda k).rows) (hWeights : ∑ j,weights.read j=Qv)
    (hGood : ∀ j,GeneralPaperMeshPrefixInvariant.Good m lambda k Qv (prefixes.read j)) :
    (GeneralPaperNativeSelectorExecution.prepareTree true (fun x => x) model.rat W prepared T ready weights prefixes).2≤
      profile model W m lambda k Qv ((GeneralPaperSourceParameters.prepare k).summarySize+2) prepared.parameters.height prepared.parameters.leafCount := by
  let fields := GeneralPaperNativeProfitFieldsExecution.run true (fun x => x) model.rat W T weights prefixes ready.cached
  have hf := (GeneralPaperActualNativeProfitFields.work model W lambda Qv T ready weights prefixes hT hWeights hGood).1
  have hs := span m lambda k Qv prepared hp
  have hl := GeneralPaperNativeProfitFieldsExecution.length true (fun x => x) model.rat W T weights prefixes ready.cached
  have ht := GeneralPaperProfitTreePreparation.bit_work model.rat model.monotone W m prepared.parameters.height prepared.parameters.leafCount fields.1 hs.1 hl.symm hs.2
  change fields.2+(GeneralPaperProfitTreePreparation.run true (fun x => x) model.rat W m
    prepared.parameters.height prepared.parameters.leafCount fields.1).2+128*W≤_
  exact Nat.add_le_add_right (Nat.add_le_add hf ht) _

theorem arithmetic_work {m k : ℕ} (model : RationalCostModel) (lambda Qv T : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (hp : prepared=GeneralPaperProfitParameters.prepare m lambda k Qv)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) :
    (GeneralPaperNativeSelectorExecution.prepareTree false (fun _ => 1) model.rat 1 prepared T ready weights prefixes).2≤
      arithmeticProfile m k ((GeneralPaperSourceParameters.prepare k).summarySize+2) prepared.parameters.height prepared.parameters.leafCount := by
  let fields := GeneralPaperNativeProfitFieldsExecution.run false (fun _ => 1) model.rat 1 T weights prefixes ready.cached
  have hf := GeneralPaperNativeProfitFieldsPrice.arithmetic_work model.rat T weights prefixes ready.cached
  have hs := span m lambda k Qv prepared hp
  have hl := GeneralPaperNativeProfitFieldsExecution.length false (fun _ => 1) model.rat 1 T weights prefixes ready.cached
  have ht := GeneralPaperProfitTreePreparation.arithmetic_work m prepared.parameters.height prepared.parameters.leafCount fields.1 hs.1 hl.symm hs.2
  change fields.2+(GeneralPaperProfitTreePreparation.run false (fun _ => 1) (fun _ => 1) 1 m
    prepared.parameters.height prepared.parameters.leafCount fields.1).2+128≤_
  exact Nat.add_le_add_right (Nat.add_le_add hf ht) _

end Blotto.GeneralPaperNativeSelectorPreparationPrice
