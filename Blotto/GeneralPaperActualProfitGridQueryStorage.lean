import Blotto.GeneralPaperProfitGridQueryStorage

/-! Retained source profit parameters and actual native option fields
derive complete leaf/merge callback storage. Even unused grid merge pairs
are covered without a DP-validity, grid-rebuild or operand-census pass. -/
namespace Blotto.GeneralPaperActualProfitGridQueryStorage
open GeneralPaperProfitGridPrepare
open GeneralPaperUnsignedCellConstancy (Prefix)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem leaf (model : RationalCostModel) (W m lambda k Qv : ℕ)
    (p : GeneralPaperProfitParameters.Parameters) (hp : p=GeneralPaperProfitParameters.parameters m lambda k Qv)
    (grid : Prepared p.qProf p.width p.exponent) (hg : grid=prepare p.qProf p.width p.exponent)
    (num : ℕ) (hn : num≤2*p.qProf) :
    GeneralPaperProfitGridQueryStorage.leafWindow model W grid num≤
      GeneralPaperProfitGridQueryStorage.compact model W grid.depth (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) := by
  subst grid
  subst p
  have ho := GeneralPaperProfitGridQueryOperands.leaf_operands
    (GeneralPaperProfitParameters.parameters m lambda k Qv).qProf
    (GeneralPaperProfitParameters.parameters m lambda k Qv).width
    (GeneralPaperProfitParameters.parameters m lambda k Qv).exponent num hn
  have hs := GeneralPaperProfitGridQueryStorage.leaf_bounded model W _ _ num ho.1 ho.2.1 ho.2.2.1 ho.2.2.2
  exact hs.trans (GeneralPaperProfitGridQueryStorage.profile_compact model W _ _ _ (GeneralPaperProfitGridQueryOperands.source_word m lambda k Qv))

theorem merge (model : RationalCostModel) (W m lambda k Qv : ℕ)
    (p : GeneralPaperProfitParameters.Parameters) (hp : p=GeneralPaperProfitParameters.parameters m lambda k Qv)
    (grid : Prepared p.qProf p.width p.exponent) (hg : grid=prepare p.qProf p.width p.exponent) (i j : Fin grid.size) :
    GeneralPaperProfitGridQueryStorage.mergeWindow model W grid (grid.numerators.read i+grid.numerators.read j)≤
      GeneralPaperProfitGridQueryStorage.compact model W grid.depth (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) := by
  subst grid
  subst p
  have ho := GeneralPaperProfitGridQueryOperands.merge_operands _ _ _ i j
  have hs := GeneralPaperProfitGridQueryStorage.merge_bounded model W _ _ _ ho.1 ho.2
  exact hs.trans (GeneralPaperProfitGridQueryStorage.profile_compact model W _ _ _ (GeneralPaperProfitGridQueryOperands.source_word m lambda k Qv))

theorem ready_leaf {m k : ℕ} (model : RationalCostModel) (W Qv T : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared)
    (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (hPrepared : prepared=GeneralPaperProfitParameters.prepare m r.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (j : Fin m)
    (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (hT : T=(GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows)
    (hWeights : ∑ a,weights.read a=Qv)
    (hGood : GeneralPaperMeshPrefixInvariant.Good m r.alphabet.lambda k Qv (prefixes.read j)) :
    GeneralPaperProfitGridQueryStorage.leafWindow model W prepared.grid
      (((GeneralPaperNativeProfitLeafExecution.run true (fun w => w) model.rat W T (weights.read j)
        (prefixes.read j) (r.cached.read j)).1.read i).1)≤
      GeneralPaperProfitGridQueryStorage.compact model W prepared.grid.depth
        (GeneralPaperPowerPreparationEnvelope.operandWidth m r.alphabet.lambda k Qv) := by
  subst prepared
  rw [GeneralPaperNativeProfitLeafExecution.data true (fun w => w) model.rat W T (weights.read j)
    (prefixes.read j) (r.cached.read j) (GeneralPaperActualNativeProfitFields.meshes r j)]
  apply leaf model W m r.alphabet.lambda k Qv _ rfl _ rfl
  exact GeneralPaperNativeGridQueryPrice.numerator_bound m r.alphabet.lambda Qv T (weights.read j) (prefixes.read j) (r.cached.read j) i
    hT (GeneralPaperNativeProfitFieldsPrice.weight_bound weights Qv hWeights j) (GeneralPaperActualNativeProfitFields.meshes r j) hGood

end Blotto.GeneralPaperActualProfitGridQueryStorage
