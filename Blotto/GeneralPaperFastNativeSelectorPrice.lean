import Blotto.GeneralPaperFastRootPrice

/-! Complete fast native selector prices: weighted input/list/tree preparation,
balanced DP, root scan, backtracking, tuple conversion and zero fallback.
Every exact primitive is charged at its existing operand width. The only
budget premise is the leaf-word bound derived for actual classified sources. -/
namespace Blotto.GeneralPaperFastNativeSelectorPrice
open GeneralPaperFastRationalModel
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

def preparationProfile (C d W m lambda k Qv K h leaves : ℕ) : ℕ :=
  GeneralPaperNativeProfitFieldsPrice.profile (charge C d) W m lambda k Qv K+
    GeneralPaperProfitTreePreparation.bitProfile (charge C d) W m K h leaves+128*W

theorem preparation_bound {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W m lambda k Qv K h leaves : ℕ) :
    GeneralPaperNativeSelectorPreparationPrice.profile model W m lambda k Qv K h leaves≤
      preparationProfile C d W m lambda k Qv K h leaves := by
  unfold GeneralPaperNativeSelectorPreparationPrice.profile preparationProfile
    GeneralPaperNativeProfitFieldsPrice.profile GeneralPaperNativeProfitLeafPrice.profile
    GeneralPaperNativeProfitLeafPrice.elementProfile GeneralPaperMeshPairPrice.tailsProfile
    GeneralPaperCachedMeshIntervalQuery.cachedProfile GeneralPaperCachedMeshIntervalQuery.profile
    GeneralPaperMeshQueryEnvelope.profile GeneralPaperProfitTreePreparation.bitProfile
  dsimp only
  gcongr <;> exact hg _

def profile (C d W m lambda k Qv K J h leaves : ℕ) : ℕ :=
  preparationProfile C d W m lambda k Qv K h leaves+
    GeneralPaperFastRootPrice.profile C d W m lambda k Qv K J (lambda+1)+
    GeneralPaperRowTrimPrice.profile W m leaves+256*W

theorem profile_bound {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W m lambda k Qv K J leaves budgetWord : ℕ) (hb : budgetWord≤GeneralPaperTagHeight.word (lambda+1) 0) :
    GeneralPaperNativeSelectorPrice.profile model W m lambda k Qv K J
      (GeneralPaperProfitParameters.parameters m lambda k Qv).height leaves budgetWord≤
      profile C d W m lambda k Qv K J (GeneralPaperProfitParameters.parameters m lambda k Qv).height leaves :=
  Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add
    (preparation_bound hg W m lambda k Qv K _ leaves)
    (GeneralPaperFastRootPrice.profile_bound hg W m lambda k Qv K J (lambda+1) budgetWord hb)) _) _

def pickProfile (C d W m lambda k Qv K J h leaves : ℕ) : ℕ :=
  profile C d W m lambda k Qv K J h leaves+GeneralPaperZeroRowPrice.profile W m+128*W

theorem pick_profile_bound {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W m lambda k Qv K J leaves budgetWord : ℕ) (hb : budgetWord≤GeneralPaperTagHeight.word (lambda+1) 0) :
    GeneralPaperNativeSelectorPrice.pickProfile model W m lambda k Qv K J
      (GeneralPaperProfitParameters.parameters m lambda k Qv).height leaves budgetWord≤
      pickProfile C d W m lambda k Qv K J (GeneralPaperProfitParameters.parameters m lambda k Qv).height leaves :=
  Nat.add_le_add_right (Nat.add_le_add_right (profile_bound hg W m lambda k Qv K J leaves budgetWord hb) _) _

theorem native_pick_work {m k : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W Qv T : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (GeneralPaperUnsignedCellConstancy.Prefix k)) (B : ℚ)
    (hp : prepared=GeneralPaperProfitParameters.prepare m ready.alphabet.lambda k Qv)
    (hT : T=(GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows) (hw : ∑ j,weights.read j=Qv)
    (hgood : ∀ j,GeneralPaperMeshPrefixInvariant.Good m ready.alphabet.lambda k Qv (prefixes.read j))
    (hb : rationalWordWidth B≤GeneralPaperTagHeight.word (ready.alphabet.lambda+1) 0) :
    (GeneralPaperNativeSelectorExecution.pick true (fun x => x) model.rat W prepared T ready weights prefixes B).2≤
      pickProfile C d W m ready.alphabet.lambda k Qv ((GeneralPaperSourceParameters.prepare k).summarySize+2)
        prepared.grid.size prepared.parameters.height prepared.parameters.leafCount := by
  have hn := (GeneralPaperNativeSelectorPrice.native_work model W Qv T prepared ready weights prefixes B hp hT hw hgood).1
  have hh : prepared.parameters.height=(GeneralPaperProfitParameters.parameters m ready.alphabet.lambda k Qv).height := by rw [hp]; rfl
  have hc : GeneralPaperNativeSelectorPrice.pickProfile model W m ready.alphabet.lambda k Qv
      ((GeneralPaperSourceParameters.prepare k).summarySize+2) prepared.grid.size prepared.parameters.height prepared.parameters.leafCount (rationalWordWidth B)≤
      pickProfile C d W m ready.alphabet.lambda k Qv ((GeneralPaperSourceParameters.prepare k).summarySize+2)
        prepared.grid.size prepared.parameters.height prepared.parameters.leafCount := by
    rw [hh]
    exact pick_profile_bound hg W m ready.alphabet.lambda k Qv _ _ _ _ hb
  exact hn.trans hc

end Blotto.GeneralPaperFastNativeSelectorPrice
