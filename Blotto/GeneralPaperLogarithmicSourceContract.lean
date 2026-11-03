import Blotto.GeneralPaperLogarithmicSourceReference

/-! Attach the quantitative logarithmic word bound to the original native
source-core time and retained-capacity contract. Both rich/poor budgets and
the stored first trajectory keep their existing exact native identities.
Final source/compiler soft-O exponents and original-game input joins remain. -/
namespace Blotto.GeneralPaperLogarithmicSourceContract
open GeneralPaperSourceWordGrowth GeneralPaperLogarithmicSourceReference
open GeneralPaperFastRationalModel GeneralPaperInitializerPreparedPoint
open GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def Core (actual : RationalCostModel) (C d : ℕ) (x : Input) (firstReciprocal : Bool) (count : ℕ) : Prop :=
  let Bc := ownBudget x.m x.k (x.b:ℝ) x.reciprocal
  let Br := opposingBudget x.m x.k (x.b:ℝ) x.reciprocal
  let W := width C d x
  let ready := (GeneralPaperPreparedSharedSource.prepare actual x.k x.Qv x.b x.weights Bc Br).1
  let a := ready.1.1.1.2
  let c := ready.2.source
  let hc : c=GeneralPaperMaterializedPowerCache.specification x.m a.lambda x.k x.Qv := by
    dsimp only [c,a,ready]
    rw [GeneralPaperPreparedSharedSource.data]
    rfl
  let first := prepare a x.k x.Qv x.weights (ownBudget x.m x.k (x.b:ℝ) firstReciprocal) (opposingBudget x.m x.k (x.b:ℝ) firstReciprocal)
  (GeneralPaperGeometricSourceExecution.run true (fun w => w) actual W x.k x.Qv a c hc ready.1.2 count).2≤
    GeneralPaperFastSourceMajorant.profile C d W x.m x.k x.Qv a count ∧
  GeneralPaperPrecallResidentStorage.inputs W x.m x.k x.Qv x.b Bc Br+
    ((GeneralPaperClassifierResultStorage.frontFootprint W ready.1.1+
      (GeneralPaperMaterializedCacheStorage.gridFootprint W ready.2+GeneralPaperEncodedSharedSource.footprint W ready.1.2+
        GeneralPaperEpochResidentStorage.footprint W x.k x.Qv a x.weights Bc Br 0 0)+64*W)+
      GeneralPaperSourceLifetimeStorage.window actual W x.k x.Qv a c hc x.weights Bc Br count)+
    GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows (execute first a x.k first.trajectory.epochs).2<2^W

theorem native_core {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d)
    (x : Input) (firstReciprocal : Bool) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs) :
    Core actual C d x firstReciprocal count :=
  GeneralPaperFastClassifiedSourceContract.time_and_retained_capacity hg x.k x.Qv x.B x.b x.hb x.hB
    x.reciprocal firstReciprocal x.weights x.weight_sum count he

theorem logarithmic_contract {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d) :
    ∃ A : ℕ,∀ (x : Input) (firstReciprocal : Bool) (count : ℕ),
      count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs →
      width C d x≤A*logSize x ∧ Core actual C d x firstReciprocal count := by
  rcases GeneralPaperLogarithmicSourceReference.width_tight C d with ⟨A,hA⟩
  exact ⟨A,fun x first count he => ⟨hA x,native_core hg x first count he⟩⟩

end Blotto.GeneralPaperLogarithmicSourceContract
