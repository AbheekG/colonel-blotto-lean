import Blotto.GeneralPaperSourcePriceMonotonicity

/-! A complete fast source price with every remaining Rat term interpreted by
an explicit logarithmic majorant. It bounds the original native execution;
only closed profiles are compared. Actual budgets, grids, trees, trajectory
and prepared cache are unchanged, and no source replay is introduced. -/
namespace Blotto.GeneralPaperFastSourceMajorant
open GeneralPaperFastRationalModel GeneralPaperCodeAlphabet
open GeneralPaperInitializerPreparedPoint
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

def profile (C d W m k Qv : ℕ) (a : Alphabet) (count : ℕ) : ℕ :=
  GeneralPaperSelectorRefinedSourcePrice.profile (GeneralPaperFastRationalMajorant.model C d) C d W m k Qv a count

theorem bound {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d)
    (W m k Qv : ℕ) (a : Alphabet) (count : ℕ) :
    GeneralPaperSelectorRefinedSourcePrice.profile actual C d W m k Qv a count≤profile C d W m k Qv a count :=
  GeneralPaperSourcePriceMonotonicity.source actual _ (GeneralPaperFastRationalMajorant.dominates hg) C d W m k Qv a count

theorem native_work {m : ℕ} {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d)
    (W k Qv : ℕ) (a : Alphabet) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (hbc : rationalWordWidth Bc≤GeneralPaperTagHeight.word (a.lambda+1) 0)
    (hbr : rationalWordWidth Br≤GeneralPaperTagHeight.word (a.lambda+1) 0) :
    let shared := GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br
    (GeneralPaperGeometricSourceExecution.run true (fun x => x) actual W k Qv a c hc shared count).2≤profile C d W m k Qv a count :=
  (GeneralPaperSelectorRefinedSourcePrice.native_work hg W k Qv a c hc weights Bc Br hw count he hbc hbr).trans
    (bound hg W m k Qv a count)

theorem classified_work {m : ℕ} {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d)
    (W k Qv : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv)
    (weights : FixedArrayTable m ℕ) (hw : ∑ j,weights.read j=Qv) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs) :
    let a := GeneralPaperProxyParameters.alphabet m k
    let shared := GeneralPaperCatalogueShared.prepare a k Qv weights (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
    (GeneralPaperGeometricSourceExecution.run true (fun x => x) actual W k Qv a c hc shared count).2≤profile C d W m k Qv a count :=
  (GeneralPaperSelectorRefinedSourcePrice.classified_work hg W k Qv b hb reciprocal c hc weights hw count he).trans
    (bound hg W m k Qv _ count)

theorem classified_prepared {m : ℕ} {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d)
    (W k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) (reciprocal : Bool) (weights : FixedArrayTable m ℕ)
    (hw : ∑ j,weights.read j=Qv) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs) :
    let Bc := ownBudget m k (b:ℝ) reciprocal
    let Br := opposingBudget m k (b:ℝ) reciprocal
    let ready := (GeneralPaperPreparedSharedSource.prepare actual k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let c := ready.2.source
    let hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv := by
      dsimp only [c,a,ready]
      rw [GeneralPaperPreparedSharedSource.data]
      rfl
    (GeneralPaperGeometricSourceExecution.run true (fun x => x) actual W k Qv a c hc ready.1.2 count).2≤profile C d W m k Qv a count :=
  (GeneralPaperSelectorRefinedSourcePrice.classified_prepared hg W k Qv b hb reciprocal weights hw count he).trans
    (bound hg W m k Qv _ count)

end Blotto.GeneralPaperFastSourceMajorant
