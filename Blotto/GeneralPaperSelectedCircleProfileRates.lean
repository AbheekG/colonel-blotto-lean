import Blotto.GeneralPaperNativePreparationReferenceContract

/-! Branch-sensitive growth of the actual description cache profile. Capping
the unused representative parameter is erased analysis only. On the native
circle branch it is exactly the original record; the direct branch has no
circle construction. No native reduction or constructor changes. -/
namespace Blotto.GeneralPaperSelectedCircleProfileRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperCacheConstructionGrowth GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

def capped {n : ℕ} (o : GeneralPaperReducedValuesDriver.Output n) : GeneralPaperReducedValuesDriver.Output n :=
  {o with representatives:=min o.representatives o.m}

theorem capped_eq {n : ℕ} (o : GeneralPaperReducedValuesDriver.Output n) (h : o.representatives≤o.m) : capped o=o := by
  unfold capped
  rw [Nat.min_eq_left h]

theorem owner_le {n : ℕ} (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperOriginalReductionRetainedStorage.footprint W (capped o)≤
      GeneralPaperOriginalReductionRetainedStorage.footprint W o := by
  have h := Nat.add_le_add_left (binaryWordWidth_mono (Nat.min_le_left o.representatives o.m)) 1
  change natBits (min o.representatives o.m)≤natBits o.representatives at h
  unfold GeneralPaperOriginalReductionRetainedStorage.footprint capped
  dsimp only
  omega

theorem selected_le {n : ℕ} (model : RationalCostModel) (W T K H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (h : o.replaced=true → o.representatives≤o.m) :
    GeneralPaperStrategyDescriptionConstructionStorage.childProfile model W T K H o≤
      GeneralPaperCachedPairConstructionStorage.profile model W T K H (capped o) := by
  unfold GeneralPaperStrategyDescriptionConstructionStorage.childProfile
  split_ifs with he
  · rw [capped_eq o (h he)]
  · exact Nat.zero_le _

theorem selected_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n : Input → ℕ) (o : (x : Input) → GeneralPaperReducedValuesDriver.Output (n x))
    (hW : Tight W) (hn : Small n) (hM : ∀ x,(o x).m=x.m)
    (hG : Small (fun x => (o x).classified.light.size)) (hR : Small (fun x => (o x).representatives))
    (hMass : Small (fun x => (o x).classified.lightWeight)) (hGN : ∀ x,(o x).classified.light.size≤n x)
    (hHeavy : ∀ x,(o x).classified.heavy.size≤x.m)
    (hBranch : ∀ x,(o x).replaced=true → (o x).representatives≤(o x).m)
    (hOwner : Linear (fun x => GeneralPaperOriginalReductionRetainedStorage.footprint (W x) (o x)) n) :
    Soft (rate n) (fun x => GeneralPaperStrategyDescriptionConstructionStorage.childProfile model (W x)
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k).rows
      (GeneralPaperProxyParameters.prepare x.m x.k).K (GeneralPaperSourcePairAnchorHeights.width x.m x.k) (o x)) := by
  have hRep : Small (fun x => (capped (o x)).representatives) := by
    change Small (fun x => min (o x).representatives (o x).m)
    fun_prop
  have hOwner' : Linear (fun x => GeneralPaperOriginalReductionRetainedStorage.footprint (W x) (capped (o x))) n :=
    GeneralPaperSourceSoftBounds.dominated hOwner (fun x => owner_le (W x) (o x))
  have hRate := pair_rate hg W n (fun x => capped (o x)) hW hn hM hG hRep hMass hGN hHeavy
    (fun x => by change min (o x).representatives (o x).m≤x.m;rw [←hM x];exact Nat.min_le_right _ _) hOwner'
  exact GeneralPaperSourceSoftBounds.dominated hRate (fun x => selected_le model (W x) _ _ _ (o x) (hBranch x))

end Blotto.GeneralPaperSelectedCircleProfileRates
