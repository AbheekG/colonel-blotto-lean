import Blotto.GeneralPaperProfitTreePreparation
import Blotto.GeneralPaperActualNativeProfitFields

/-! Retained paper parameters supply the actual root span and all local
tree-control words. Both native optimizer input families have exactly m
fields, so no length census, new ceiling or height oracle executes. -/
namespace Blotto.GeneralPaperSelectedProfitTreePrice
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem height_bound (m lambda k Qv : ℕ) :
    (GeneralPaperProfitParameters.parameters m lambda k Qv).height≤binaryWordWidth m :=
  GeneralPaperPowerCeiling.loop_depth m 1 (by decide)

theorem source_word (m lambda k Qv : ℕ) :
    GeneralPaperTreeHalfPrice.width (GeneralPaperProfitParameters.parameters m lambda k Qv).height≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have hh := height_bound m lambda k Qv
  have hm := binaryWordWidth_mono (show m≤m+1 by omega)
  have h1 : binaryWordWidth 1=1 := by decide
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  unfold GeneralPaperTreeHalfPrice.width GeneralPaperRankOperands.width GeneralPaperPowerPreparationEnvelope.operandWidth
    GeneralPaperSourcePreparationSizes.measure at *
  simp only [Nat.zero_add,h1]
  omega

theorem work {R : Type} [Zero R] {K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W m lambda k Qv : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (hPrepared : prepared=GeneralPaperProfitParameters.prepare m lambda k Qv)
    (input : List (GeneralPaperOrderedProfitTreeBuild.WeightedField R K)) (hLen : input.length=m) :
    (GeneralPaperProfitTreePreparation.run true (fun x => x) primitive W m prepared.parameters.height prepared.parameters.leafCount input).2≤
      GeneralPaperProfitTreePreparation.bitProfile primitive W m K prepared.parameters.height prepared.parameters.leafCount ∧
    (GeneralPaperProfitTreePreparation.run false (fun _ => 1) (fun _ => 1) 1 m prepared.parameters.height prepared.parameters.leafCount input).2≤
      GeneralPaperProfitTreePreparation.arithmeticProfile m K prepared.parameters.height prepared.parameters.leafCount := by
  subst prepared
  have hs := GeneralPaperProfitParameters.leaf_count_spec m lambda k Qv
  have hf := GeneralPaperProfitParameters.covers_fields m lambda k Qv
  exact ⟨GeneralPaperProfitTreePreparation.bit_work primitive hMono W m _ _ input hs hLen.symm hf,
    GeneralPaperProfitTreePreparation.arithmetic_work m _ _ input hs hLen.symm hf⟩

theorem native_input_length {m k : ℕ} (T : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (GeneralPaperUnsignedCellConstancy.Prefix k)) :
    (GeneralPaperOrderedNativeProfitOptimizer.weightedFields k T weights prefixes ready.cached).length=m := by
  unfold GeneralPaperOrderedNativeProfitOptimizer.weightedFields
  exact List.length_ofFn

theorem native_work {m k : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W lambda Qv T : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (hPrepared : prepared=GeneralPaperProfitParameters.prepare m lambda k Qv)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (GeneralPaperUnsignedCellConstancy.Prefix k)) :
    let input := GeneralPaperOrderedNativeProfitOptimizer.weightedFields k T weights prefixes ready.cached
    let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
    (GeneralPaperProfitTreePreparation.run true (fun x => x) primitive W m prepared.parameters.height prepared.parameters.leafCount input).2≤
      GeneralPaperProfitTreePreparation.bitProfile primitive W m K prepared.parameters.height prepared.parameters.leafCount ∧
    (GeneralPaperProfitTreePreparation.run false (fun _ => 1) (fun _ => 1) 1 m prepared.parameters.height prepared.parameters.leafCount input).2≤
      GeneralPaperProfitTreePreparation.arithmeticProfile m K prepared.parameters.height prepared.parameters.leafCount :=
  work primitive hMono W m lambda k Qv prepared hPrepared _ (native_input_length T ready weights prefixes)

end Blotto.GeneralPaperSelectedProfitTreePrice
