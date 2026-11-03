import Blotto.GeneralPaperSharpSourceSpaceRate

/-! Sharp quantitative native source storage shares the derived bit word
with both source time bounds and the native real/bit data agreement. All
input/front/cache/shared/epoch owners and a first trajectory are retained. -/
namespace Blotto.GeneralPaperSharpSourceSpaceContract
open GeneralPaperSourceWordGrowth GeneralPaperSharpSourceSpaceRate GeneralPaperClassifierSpaceRates
open GeneralPaperFastRationalModel GeneralPaperInitializerPreparedPoint
open GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384

noncomputable def live (actual : RationalCostModel) (W : ℕ) (x : Input)
    (firstReciprocal : Bool) (count : ℕ) : ℕ :=
  let Bc := ownBudget x.m x.k (x.b:ℝ) x.reciprocal
  let Br := opposingBudget x.m x.k (x.b:ℝ) x.reciprocal
  let ready := (GeneralPaperPreparedSharedSource.prepare actual x.k x.Qv x.b x.weights Bc Br).1
  let a := ready.1.1.1.2
  let c := ready.2.source
  let hc : c=GeneralPaperMaterializedPowerCache.specification x.m a.lambda x.k x.Qv := by
    dsimp only [c,a,ready]
    rw [GeneralPaperPreparedSharedSource.data]
    rfl
  let first := prepare a x.k x.Qv x.weights
    (ownBudget x.m x.k (x.b:ℝ) firstReciprocal) (opposingBudget x.m x.k (x.b:ℝ) firstReciprocal)
  GeneralPaperPrecallResidentStorage.inputs W x.m x.k x.Qv x.b Bc Br+
    ((GeneralPaperClassifierResultStorage.frontFootprint W ready.1.1+
      (GeneralPaperMaterializedCacheStorage.gridFootprint W ready.2+
        GeneralPaperEncodedSharedSource.footprint W ready.1.2+
        GeneralPaperEpochResidentStorage.footprint W x.k x.Qv a x.weights Bc Br 0 0)+64*W)+
      GeneralPaperSourceLifetimeStorage.window actual W x.k x.Qv a c hc x.weights Bc Br count)+
    GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows (execute first a x.k first.trajectory.epochs).2

theorem live_profile {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d)
    (W : Input → ℕ) (x : Input) (firstReciprocal : Bool) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs) :
    live actual (W x) x firstReciprocal count≤profile C d W x := by
  have hb : (0:ℝ)<x.b ∧ (x.b:ℝ)<1 := by exact_mod_cast x.hb
  have hc := GeneralPaperSourceBudgetWidths.own_height x.m x.k (x.b:ℝ) hb x.reciprocal
  have hr := GeneralPaperSourceBudgetWidths.opposing_height x.m x.k (x.b:ℝ) hb x.reciprocal
  have h := GeneralPaperFastSourceReference.prepared_live_bound actual (W x) x.k x.Qv x.B
    ((alphabet x).lambda+1) ((alphabet x).lambda+1) x.b x.hb x.weights
    (ownBudget x.m x.k (x.b:ℝ) x.reciprocal) (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal)
    (ownBudget x.m x.k (x.b:ℝ) firstReciprocal) (opposingBudget x.m x.k (x.b:ℝ) firstReciprocal)
    x.weight_sum x.hB hc hr count he
  have hm := GeneralPaperFastSourceReference.dominates hg (W x) x.k x.Qv x.B
    ((alphabet x).lambda+1) ((alphabet x).lambda+1) (alphabet x) x.weights
    (ownBudget x.m x.k (x.b:ℝ) x.reciprocal) (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal)
  simp only [GeneralPaperPreparedSharedSource.data] at h
  unfold live profile
  simp only [GeneralPaperPreparedSharedSource.data]
  exact h.trans hm

theorem prefix_space_bound {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d) :
    ∃ A e : ℕ,∀ (x : Input) (firstReciprocal : Bool) (count : ℕ),
      count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs →
      live actual (GeneralPaperLogarithmicSourceReference.width C d x) x firstReciprocal count≤
        A*rate x*(logSize x)^e := by
  rcases common_word_bound C d with ⟨A,e,hA⟩
  exact ⟨A,e,fun x first count he => (live_profile hg _ x first count he).trans (hA x)⟩

theorem paper_space_bound {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d) :
    ∃ A e : ℕ,∀ (x : Input) (firstReciprocal : Bool) (count : ℕ),1≤x.m →
      count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs →
      live actual (GeneralPaperLogarithmicSourceReference.width C d x) x firstReciprocal count≤
        A*paperRate x*(logSize x)^e := by
  rcases paper_profile_bound C d with ⟨A,e,hA⟩
  exact ⟨A,e,fun x first count hm he => (live_profile hg _ x first count he).trans (hA x hm)⟩

theorem paper_models_space_and_capacity {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d) :
    ∃ Ar er Ab eb As es : ℕ,∀ (x : Input) (firstReciprocal : Bool) (count : ℕ),1≤x.m →
      count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs →
      GeneralPaperSharpSourceRealContract.NativeTime actual x count
        (Ar*GeneralPaperSharpSourceRealRate.paperRate x*(GeneralPaperSourceCoreLogBound.coreLog x)^er) ∧
      GeneralPaperSharpSourceBitContract.NativeTime actual C d x count
        (Ab*GeneralPaperSharpSourceBitRate.paperRate x*(logSize x)^eb) ∧
      live actual (GeneralPaperLogarithmicSourceReference.width C d x) x firstReciprocal count≤
        As*paperRate x*(logSize x)^es ∧
      GeneralPaperLogarithmicSourceContract.Core actual C d x firstReciprocal count ∧
      GeneralPaperSharpSourceRealContract.OutputAgreement actual x count
        (GeneralPaperLogarithmicSourceReference.width C d x) := by
  rcases GeneralPaperSharpSourceRealContract.paper_models_and_capacity hg with ⟨Ar,er,Ab,eb,ht⟩
  rcases paper_space_bound hg with ⟨As,es,hs⟩
  refine ⟨Ar,er,Ab,eb,As,es,?_⟩
  intro x first count hm he
  have h := ht x first count hm he
  exact ⟨h.1,h.2.1,hs x first count hm he,h.2.2.1,h.2.2.2⟩

end Blotto.GeneralPaperSharpSourceSpaceContract
