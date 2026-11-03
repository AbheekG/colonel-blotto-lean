import Blotto.GeneralPaperFastSourceReference

/-! One common derived fast-model reference width joins actual prepared
source time and retained-input/front/cache/first-trajectory address capacity.
Both rich/poor normalizations derive their own budget heights; only the
one-time original rational input height remains explicit. This is the
source-core contract, not the final compiler/equilibrium/soft-O theorem. -/
namespace Blotto.GeneralPaperFastClassifiedSourceContract
open GeneralPaperFastRationalModel GeneralPaperInitializerPreparedPoint
open GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

theorem time_and_retained_capacity {m : ℕ} {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d)
    (k Qv B : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B)
    (reciprocal firstReciprocal : Bool) (weights : FixedArrayTable m ℕ) (hw : ∑ j,weights.read j=Qv)
    (count : ℕ) (he : count≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs) :
    let H := GeneralPaperSourceBudgetWidths.height m k
    let Bc := ownBudget m k (b:ℝ) reciprocal
    let Br := opposingBudget m k (b:ℝ) reciprocal
    let W := GeneralPaperFastSourceReference.preparedWidth C d k Qv B H H weights Bc Br
    let ready := (GeneralPaperPreparedSharedSource.prepare actual k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let c := ready.2.source
    let hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv := by
      dsimp only [c,a,ready]
      rw [GeneralPaperPreparedSharedSource.data]
      rfl
    let first := prepare a k Qv weights (ownBudget m k (b:ℝ) firstReciprocal) (opposingBudget m k (b:ℝ) firstReciprocal)
    (GeneralPaperGeometricSourceExecution.run true (fun x => x) actual W k Qv a c hc ready.1.2 count).2≤
      GeneralPaperFastSourceMajorant.profile C d W m k Qv a count ∧
    GeneralPaperPrecallResidentStorage.inputs W m k Qv b Bc Br+
      ((GeneralPaperClassifierResultStorage.frontFootprint W ready.1.1+
        (GeneralPaperMaterializedCacheStorage.gridFootprint W ready.2+GeneralPaperEncodedSharedSource.footprint W ready.1.2+
          GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br 0 0)+64*W)+
        GeneralPaperSourceLifetimeStorage.window actual W k Qv a c hc weights Bc Br count)+
      GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows (execute first a k first.trajectory.epochs).2<2^W := by
  let H := GeneralPaperSourceBudgetWidths.height m k
  let Bc := ownBudget m k (b:ℝ) reciprocal
  let Br := opposingBudget m k (b:ℝ) reciprocal
  let W := GeneralPaperFastSourceReference.preparedWidth C d k Qv B H H weights Bc Br
  have hbR : 0<(b:ℝ) ∧ (b:ℝ)<1 := by exact_mod_cast hb
  have ht := GeneralPaperFastSourceMajorant.classified_prepared hg W k Qv b hb reciprocal weights hw count he
  have hs := GeneralPaperFastSourceReference.prepared_live_capacity hg k Qv B H H b hb weights Bc Br
    (ownBudget m k (b:ℝ) firstReciprocal) (opposingBudget m k (b:ℝ) firstReciprocal) hw hB
    (GeneralPaperSourceBudgetWidths.own_height m k (b:ℝ) hbR reciprocal)
    (GeneralPaperSourceBudgetWidths.opposing_height m k (b:ℝ) hbR reciprocal) count he
  exact ⟨ht,hs⟩

end Blotto.GeneralPaperFastClassifiedSourceContract
