import Blotto.GeneralPaperSourceScoreStorage
import Blotto.GeneralPaperBasisStorageRates

/-! Growth and positive-width scaling of the actual source-DP layer storage
profile. Encoded work counters remain polylogarithmic. The complete native
scan stack is included, while fast rational scratch is charged only at the
maximum active primitive. Full compiler space and matrix lifetimes remain
separate joins. -/
namespace Blotto.GeneralPaperScoreStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

@[fun_prop]
theorem cap_length : Rated (fun x => binaryWordWidth (GeneralPaperProxyParameters.prepare x.m x.k).qbar) 0 1 0 := by
  apply GeneralPaperSourceSoftBounds.dominated (g:=fun x => (alphabet x).lambda+1)
  · change Rated (fun x => (alphabet x).lambda+1) 0 1 0
    source_space
  · intro x
    exact GeneralPaperSourceBudgetWidths.cap_height x.m x.k

@[fun_prop]
theorem anchor_height : Rated (fun x => GeneralPaperSourceScoreHeights.anchorHeight x.m x.k) 0 1 0 := by
  unfold GeneralPaperSourceScoreHeights.anchorHeight
  source_space

@[fun_prop]
theorem anchor_small : Small (fun x => GeneralPaperSourceScoreHeights.anchorHeight x.m x.k) := by
  apply GeneralPaperSourceWordGrowth.dominated (g:=fun x => 2*((alphabet x).lambda+1))
  · fun_prop
  · intro x
    have hC := GeneralPaperSourceAlphabetLower.scale_width (alphabet x)
    have hQ := GeneralPaperSourceBudgetWidths.cap_height x.m x.k
    unfold GeneralPaperSourceScoreHeights.anchorHeight
    change binaryWordWidth (alphabet x).C+binaryWordWidth (GeneralPaperProxyParameters.prepare x.m x.k).qbar≤_
    change binaryWordWidth (GeneralPaperProxyParameters.prepare x.m x.k).qbar≤(alphabet x).lambda+1 at hQ
    omega

@[fun_prop]
theorem scores : Rated (fun x => (GeneralPaperProxyParameters.prepare x.m x.k).S) 1 0 1 := by
  apply GeneralPaperSourceSoftBounds.dominated (g:=fun x => 2*(x.m*(GeneralPaperProxyParameters.prepare x.m x.k).K)+1)
  · change Rated (fun x => 2*(x.m*(GeneralPaperProxyParameters.prepare x.m x.k).K)+1) 1 0 1
    source_space
  · intro x
    rw [(GeneralPaperProxyParameters.data x.m x.k).2.1,(GeneralPaperProxyParameters.data x.m x.k).1]
    by_cases hm : x.m=0
    · rw [hm]
      change (GeneralPaperPowerCeiling.ceiling (0*(GeneralPaperScoreScaleParameters.powerRun (7+x.k)).power)).power≤
        2*(0*(GeneralPaperScoreScaleParameters.prepare 0 x.k).K)+1
      simp only [Nat.zero_mul,Nat.mul_zero,Nat.zero_add]
      change (GeneralPaperPowerCeiling.loop 0 1 (by decide)).power≤1
      rw [GeneralPaperPowerCeiling.loop,ite_eq_left (Nat.zero_le 1)]
    · have h := GeneralPaperScoreScaleParameters.scale_upper x.m x.k (by omega)
      omega

theorem scaling (model : RationalCostModel) (m k : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => GeneralPaperSourceScoreStorage.profile model W m k) := by
  unfold GeneralPaperSourceScoreStorage.profile GeneralPaperScoreLifetimeStorage.layerProfile
    GeneralPaperScoreLifetimeStorage.callerProfile GeneralPaperScoreLifetimeStorage.workCap
    GeneralPaperScoreConstructionStorage.stepProfile GeneralPaperScoreConstructionStorage.constructorProfile
    GeneralPaperScoreScanStorage.profile GeneralPaperScoreScanStorage.frameProfile GeneralPaperScoreScanStorage.workCap
    GeneralPaperScoreDPBits.profile GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreDPBits.stepProfile
  dsimp only
  fun_prop

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperSourceScoreStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hR : Rated W 0 0 0 := poly (poly_tight W hW)
  have hSmall := of_tight hW
  refine ⟨_,_,_,by
    unfold GeneralPaperSourceScoreStorage.profile GeneralPaperScoreLifetimeStorage.layerProfile
      GeneralPaperScoreLifetimeStorage.callerProfile GeneralPaperScoreLifetimeStorage.workCap
      GeneralPaperScoreConstructionStorage.stepProfile GeneralPaperScoreConstructionStorage.constructorProfile
      GeneralPaperScoreScanStorage.profile GeneralPaperScoreScanStorage.frameProfile GeneralPaperScoreScanStorage.workCap
      GeneralPaperScoreDPBits.profile GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreDPBits.stepProfile
      GeneralPaperScoreTableStorage.tableProfile GeneralPaperScoreSelectionStorage.optionProfile
      GeneralPaperScoreSelectionStorage.selectionProfile GeneralPaperEncodedScalarStorage.natBits
      GeneralPaperScoreBitPrimitive.resourceWidth
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(2,1,1) := rfl

theorem profile_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Rated (fun x =>
    GeneralPaperSourceScoreStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) 2 1 1 :=
  (certificate C d W hW).bound

theorem at_one_small (C d : ℕ) : Small (fun x =>
    GeneralPaperSourceScoreStorage.profile (GeneralPaperFastRationalMajorant.model C d) 1 x.m x.k) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small (profile_rate C d (fun _ => 1) (tight_constant 1))
  unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

theorem common_word_bound (C d : ℕ) : ∃ A e : ℕ,∀ x,
    GeneralPaperSourceScoreStorage.profile (GeneralPaperFastRationalMajorant.model C d)
      (GeneralPaperCompilerReference.width C d x) x.m x.k≤
        A*monomial 2 1 1 x*(logSize x)^e :=
  profile_rate C d _ (width_tight C d)

@[gcongr]
theorem word_monotone {a b : ℕ} (h : a≤b) : binaryWordWidth a≤binaryWordWidth b := binaryWordWidth_mono h

theorem profile_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    GeneralPaperSourceScoreStorage.profile actual W m k≤GeneralPaperSourceScoreStorage.profile upper W m k := by
  unfold GeneralPaperSourceScoreStorage.profile GeneralPaperScoreLifetimeStorage.layerProfile
    GeneralPaperScoreLifetimeStorage.callerProfile GeneralPaperScoreLifetimeStorage.workCap
    GeneralPaperScoreConstructionStorage.stepProfile GeneralPaperScoreConstructionStorage.constructorProfile
    GeneralPaperScoreScanStorage.profile GeneralPaperScoreScanStorage.frameProfile GeneralPaperScoreScanStorage.workCap
    GeneralPaperScoreDPBits.profile GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreDPBits.stepProfile
    GeneralPaperEncodedScalarStorage.natBits
  dsimp only
  gcongr <;> exact h _

theorem actual_profile_rate {actual : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth actual C d) (W : Input → ℕ) (hW : Tight W) :
    Rated (fun x => GeneralPaperSourceScoreStorage.profile actual (W x) x.m x.k) 2 1 1 :=
  GeneralPaperSourceSoftBounds.dominated (profile_rate C d W hW)
    (fun x => profile_mono actual (GeneralPaperFastRationalMajorant.model C d)
      (GeneralPaperFastRationalMajorant.dominates hg) (W x) x.m x.k)

theorem actual_common_word_bound {actual : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth actual C d) : ∃ A e : ℕ,∀ x,
    GeneralPaperSourceScoreStorage.profile actual (GeneralPaperCompilerReference.width C d x) x.m x.k≤
      A*monomial 2 1 1 x*(logSize x)^e := actual_profile_rate hg _ (width_tight C d)

end Blotto.GeneralPaperScoreStorageRates
