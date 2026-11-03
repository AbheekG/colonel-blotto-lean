import Blotto.GeneralPaperDeltaStepStorage

/-! Native delta array fills count all reserved old/new buffers, complete
returns, constructor frames and controls, plus one guarded active callback.
Empty arrays and the finished prefix select no callback. -/
namespace Blotto.GeneralPaperDeltaArrayStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshPrefixInvariant (Good)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def unsignedActive {n k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (response : Bool)
    (cdfPrefix tailPrefix : Prefix k) (plan : GeneralPaperQueryLossCounts.Plan k n) (count : ℕ) : ℕ :=
  if h : count<n then GeneralPaperDeltaStepStorage.unsignedWindow model W mesh response cdfPrefix tailPrefix plan ⟨count,h⟩+32*W else 0

def signedActive {n k : ℕ} (model : RationalCostModel) (W mesh U bid : ℕ)
    (prefixes : Prefix k) (plan : GeneralPaperSignedUpdatePlan.Plan k n) (count : ℕ) : ℕ :=
  if h : count<n then GeneralPaperDeltaStepStorage.signedWindow model W mesh U bid prefixes plan ⟨count,h⟩+32*W else 0

def unsignedWindow {n k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (response : Bool)
    (cdfPrefix tailPrefix : Prefix k) (plan : GeneralPaperQueryLossCounts.Plan k n) (count : ℕ) (hc : count≤n) : ℕ :=
  GeneralPaperNativeNatFillStorage.window W
      (GeneralPaperDeltaArrayExecution.unsignedElement true model.rat W mesh response cdfPrefix tailPrefix plan) count hc+
    unsignedActive model W mesh response cdfPrefix tailPrefix plan count+256*W

def signedWindow {n k : ℕ} (model : RationalCostModel) (W mesh U bid : ℕ)
    (prefixes : Prefix k) (plan : GeneralPaperSignedUpdatePlan.Plan k n) (count : ℕ) (hc : count≤n) : ℕ :=
  GeneralPaperNativeNatFillStorage.window W
      (GeneralPaperDeltaArrayExecution.signedElement true model.rat W mesh U bid prefixes plan) count hc+
    signedActive model W mesh U bid prefixes plan count+256*W

def unsignedProfile (model : RationalCostModel) (W m lambda k Qv n : ℕ) : ℕ :=
  GeneralPaperNativeNatFillStorage.profile W n (8*(GeneralPaperSourceParameters.prepare k).meshDenominator)+
    GeneralPaperDeltaStepStorage.unsignedProfile model W m lambda k Qv n+288*W

def signedProfile (model : RationalCostModel) (W m lambda k Qv n : ℕ) : ℕ :=
  GeneralPaperNativeNatFillStorage.profile W n (8*(GeneralPaperSourceParameters.prepare k).meshDenominator)+
    GeneralPaperDeltaStepStorage.signedProfile model W m lambda k Qv n+288*W

theorem unsigned_bounded {n k : ℕ} (model : RationalCostModel) (W m lambda Qv mesh : ℕ) (response : Bool)
    (cdfPrefix tailPrefix : Prefix k) (plan : GeneralPaperQueryLossCounts.Plan k n) (count : ℕ) (hc : count≤n)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hCDF : Good m lambda k Qv cdfPrefix) (hTail : Good m lambda k Qv tailPrefix) :
    unsignedWindow model W mesh response cdfPrefix tailPrefix plan count hc≤unsignedProfile model W m lambda k Qv n := by
  have hv : ∀ q,(GeneralPaperDeltaArrayExecution.unsignedElement true model.rat W mesh response cdfPrefix tailPrefix plan q).1≤
      8*(GeneralPaperSourceParameters.prepare k).meshDenominator := by
    intro q
    exact (GeneralPaperDeltaStepStorage.unsigned_value model W m lambda Qv mesh response cdfPrefix tailPrefix plan q hm hCDF hTail).trans_eq (by rw [hm])
  have hfill := GeneralPaperNativeNatFillStorage.bounded W _ _ hv count hc
  have hactive : unsignedActive model W mesh response cdfPrefix tailPrefix plan count≤
      GeneralPaperDeltaStepStorage.unsignedProfile model W m lambda k Qv n+32*W := by
    unfold unsignedActive
    split
    · exact Nat.add_le_add_right (GeneralPaperDeltaStepStorage.unsigned_bounded model W m lambda Qv mesh response cdfPrefix tailPrefix plan _ hm hCDF hTail) _
    · exact Nat.zero_le _
  unfold unsignedWindow unsignedProfile
  omega

theorem signed_bounded {n k : ℕ} (model : RationalCostModel) (W m lambda Qv mesh U bid : ℕ)
    (prefixes : Prefix k) (plan : GeneralPaperSignedUpdatePlan.Plan k n) (count : ℕ) (hc : count≤n)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hg : Good m lambda k Qv prefixes)
    (hU : U≤2^(lambda+1)) (hbid : bid≤2^(lambda+1)) (hsafe : GeneralPaperDeltaPlanBounds.SignedSafe lambda plan) :
    signedWindow model W mesh U bid prefixes plan count hc≤signedProfile model W m lambda k Qv n := by
  have hv : ∀ q,(GeneralPaperDeltaArrayExecution.signedElement true model.rat W mesh U bid prefixes plan q).1≤
      8*(GeneralPaperSourceParameters.prepare k).meshDenominator := by
    intro q
    exact (GeneralPaperDeltaStepStorage.signed_value model W m lambda Qv mesh U bid prefixes plan q hm hg).trans_eq (by rw [hm])
  have hfill := GeneralPaperNativeNatFillStorage.bounded W _ _ hv count hc
  have hactive : signedActive model W mesh U bid prefixes plan count≤
      GeneralPaperDeltaStepStorage.signedProfile model W m lambda k Qv n+32*W := by
    unfold signedActive
    split
    · exact Nat.add_le_add_right (GeneralPaperDeltaStepStorage.signed_bounded model W m lambda Qv mesh U bid prefixes plan _ hm hg hU hbid (hsafe _).1 (hsafe _).2) _
    · exact Nat.zero_le _
  unfold signedWindow signedProfile
  omega

theorem unsigned_mono (model : RationalCostModel) (W m lambda k Qv n N : ℕ) (hn : n≤N) :
    unsignedProfile model W m lambda k Qv n≤unsignedProfile model W m lambda k Qv N := by
  have hf := GeneralPaperRankStorageMonotonicity.native_array W (8*(GeneralPaperSourceParameters.prepare k).meshDenominator) n N hn
  have hw := GeneralPaperRankStorageMonotonicity.nat_word (n+1) (N+1) (Nat.add_le_add_right hn 1)
  have hw2 := GeneralPaperRankStorageMonotonicity.nat_word (n+1+1) (N+1+1) (by omega)
  unfold unsignedProfile GeneralPaperDeltaStepStorage.unsignedProfile GeneralPaperMeshPairStorage.countsProfile
    GeneralPaperMeshPairStorage.cdfProfile GeneralPaperMeshPairStorage.tailsProfile
    GeneralPaperCachedMeshQueryStorage.prefixProfile GeneralPaperCachedMeshQueryStorage.intervalProfile GeneralPaperCachedMeshQueryStorage.controlWord
  dsimp only
  gcongr

theorem signed_mono (model : RationalCostModel) (W m lambda k Qv n N : ℕ) (hn : n≤N) :
    signedProfile model W m lambda k Qv n≤signedProfile model W m lambda k Qv N := by
  have hf := GeneralPaperRankStorageMonotonicity.native_array W (8*(GeneralPaperSourceParameters.prepare k).meshDenominator) n N hn
  have hw := GeneralPaperRankStorageMonotonicity.nat_word (n+1) (N+1) (Nat.add_le_add_right hn 1)
  unfold signedProfile GeneralPaperDeltaStepStorage.signedProfile GeneralPaperCachedMeshQueryStorage.prefixProfile GeneralPaperCachedMeshQueryStorage.controlWord
  dsimp only
  gcongr

end Blotto.GeneralPaperDeltaArrayStorage
