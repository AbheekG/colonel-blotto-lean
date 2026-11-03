import Blotto.GeneralPaperZeroRowPrice

/-! Complete native selector: one profit-input construction, one balanced
tree, one DP/root/decode and one conditional trim. The total picker also
constructs the literal zero default once. No intermediate phase is replayed. -/
namespace Blotto.GeneralPaperNativeSelectorExecution
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP
open GeneralPaperUnsignedCellConstancy (Prefix)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def prepareTree {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) :
    Tree Tag ((GeneralPaperSourceParameters.prepare k).summarySize+2) prepared.parameters.height × ℕ :=
  let fields := GeneralPaperNativeProfitFieldsExecution.run bits index price W T weights prefixes ready.cached
  let tree := GeneralPaperProfitTreePreparation.run bits index (if bits then price else fun _ => 1) W m
    prepared.parameters.height prepared.parameters.leafCount fields.1
  (tree.1,fields.2+tree.2+128*W)

theorem prepareTree_data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (hSpan : prepared.parameters.leafCount=2^prepared.parameters.height) :
    (prepareTree bits index price W prepared T ready weights prefixes).1=
      GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared T weights prefixes ready.cached := by
  have hLen := GeneralPaperNativeProfitFieldsExecution.length bits index price W T weights prefixes ready.cached
  have hFields := GeneralPaperActualNativeProfitFields.data bits index price W T ready weights prefixes
  unfold prepareTree
  dsimp only
  rw [GeneralPaperProfitTreePreparation.data bits index _ W m prepared.parameters.leafCount prepared _ hSpan hLen.symm,hFields]
  rfl

def finish {K J : ℕ} (index : ℕ → ℕ) (A m : ℕ) : Option (Fin J × List (Fin K)) → Option (FixedArrayTable m (Fin K)) × ℕ
  | none => (none,0)
  | some result => GeneralPaperRowTrimExecution.run index A m result.2

theorem finish_data {K J : ℕ} (index : ℕ → ℕ) (A m : ℕ) (result : Option (Fin J × List (Fin K))) :
    (finish index A m result).1=result.bind (fun r => GeneralPaperRowPrefix.trim m r.2) := by
  cases result with
  | none => rfl
  | some result => exact GeneralPaperRowTrimExecution.data index A m result.2

theorem native_row_eq {m k : ℕ} (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (B : ℚ) :
    GeneralPaperNativeRowOptimizer.optimize prepared T weights prefixes ready.cached B=
      (GeneralPaperOrderedProfitRoot.solve prepared.grid
        (GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared T weights prefixes ready.cached) (budget B)).bind
        (fun r => GeneralPaperRowPrefix.trim m r.2) := by
  let fields := GeneralPaperOrderedNativeProfitOptimizer.weightedFields k T weights prefixes ready.cached
  let result := GeneralPaperOrderedProfitRoot.solve prepared.grid
    (GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared T weights prefixes ready.cached) (budget B)
  have hLen : fields.length=m := GeneralPaperOrderedNativeProfitOptimizer.weighted_length k T weights prefixes ready.cached
  change (result.bind (fun r => GeneralPaperRowPrefix.trim fields.length r.2)).map (GeneralPaperRowPrefix.resize hLen)=
    result.bind (fun r => GeneralPaperRowPrefix.trim m r.2)
  cases hr : result with
  | none => rfl
  | some r => exact GeneralPaperRowTrimExecution.trim_resize hLen r.2

def run {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (B : ℚ) :
    Option (FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))) × ℕ :=
  let tree := prepareTree bits index price W prepared T ready weights prefixes
  let root := GeneralPaperOrderedRootExecution.run bits index (if bits then price else fun _ => 1) W prepared.grid tree.1 (budget B)
  let trimmed := finish index (if bits then GeneralPaperRowTrimPrice.word W m prepared.parameters.leafCount else W) m root.1
  (trimmed.1,tree.2+root.2+trimmed.2+256*W)

theorem data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (B : ℚ)
    (hSpan : prepared.parameters.leafCount=2^prepared.parameters.height) :
    (run bits index price W prepared T ready weights prefixes B).1=
      GeneralPaperNativeRowOptimizer.optimize prepared T weights prefixes ready.cached B := by
  simp only [run,finish_data,prepareTree_data bits index price W prepared T ready weights prefixes hSpan,
    GeneralPaperOrderedRootExecution.data,native_row_eq]

def pick {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (B : ℚ) :
    FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) × ℕ :=
  let chosen := run bits index price W prepared T ready weights prefixes B
  let fallback := GeneralPaperZeroRowPrice.run bits index W m k
  (chosen.1.getD fallback.1,chosen.2+fallback.2+128*W)

theorem pick_data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (B : ℚ)
    (hSpan : prepared.parameters.leafCount=2^prepared.parameters.height) :
    (pick bits index price W prepared T ready weights prefixes B).1=GeneralPaperCatalogueOptimizer.pickRow ready prepared T weights prefixes B := by
  simp only [pick,data bits index price W prepared T ready weights prefixes B hSpan,GeneralPaperZeroRowPrice.data,
    GeneralPaperCatalogueOptimizer.pickRow,GeneralPaperCatalogueOptimizer.call]

end Blotto.GeneralPaperNativeSelectorExecution
