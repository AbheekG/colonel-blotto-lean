import Blotto.GeneralPaperCatalogueGlobalLaw

/-! Within-epoch true CDFs are prefixes of the global geometric law of the
same execution. The incoming law is the actual preceding forest's law;
its mass, earlier updates and normalization are retained across boundaries.
-/
namespace Blotto.GeneralPaperCatalogueGlobalCDF
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory GeneralPaperCatalogueGlobalLaw
open GeneralPaperGeometricLevels GeneralPaperGeometricVariation
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

theorem power_global {m : ℕ} (learner : Learner) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (epochIndex count : ℕ) (hc : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) (j : Fin m) (i : ℕ) :
    GeneralPaperCatalogueEpochCDF.power learner (cacheAt (prepare a k Qv weights Bc Br) a k epochIndex) Qv weights Bc Br count j i=
      (GeneralPaperCachedMassJoin.base k:ℝ)^levels
        (fun t => history learner (prepare a k Qv weights Bc Br) a k j
          (epochIndex*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period+t)) count
        (code (Nat.two_pow_pos (treeHeight learner a.lambda)) i) := by
  let c := cacheAt (prepare a k Qv weights Bc Br) a k epochIndex
  have hw : GeneralPaperCatalogueEpochMetadata.width learner c=2^(treeHeight learner a.lambda) :=
    GeneralPaperCatalogueTreeCache.width_node _ _ a k _ learner
  have hv : (code (GeneralPaperCatalogueEpochMetadata.width_positive learner c) i).val=
      (code (Nat.two_pow_pos (treeHeight learner a.lambda)) i).val := by
    dsimp only [code]
    rw [hw]
  unfold GeneralPaperCatalogueEpochCDF.power
  congr 1
  rw [levels_sum,levels_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t<(GeneralPaperTrajectoryParameters.prepare a.lambda k).period := (Finset.mem_range.mp ht).trans_le hc
  rw [GeneralPaperCatalogueHorizon.finite_eq learner c Qv weights Bc Br t ht']
  calc
    _ = GeneralPaperCatalogueOccurrenceHistory.increment learner
        (GeneralPaperCatalogueEpochRun.selected c Qv weights Bc Br) t j
        (code (Nat.two_pow_pos (treeHeight learner a.lambda)) i).val :=
      congrArg (GeneralPaperCatalogueOccurrenceHistory.increment learner
        (GeneralPaperCatalogueEpochRun.selected c Qv weights Bc Br) t j) hv
    _ = _ := (GeneralPaperCatalogueGlobalHistory.increment_at learner (prepare a k Qv weights Bc Br) a k epochIndex t
      (GeneralPaperCatalogueGlobalHistory.period_positive a.lambda k) ht' j
      (code (Nat.two_pow_pos (treeHeight learner a.lambda)) i).val).symm

theorem current_global {m : ℕ} (learner : Learner) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (epochIndex : ℕ) (he : epochIndex≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (count : ℕ) (hc : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) (j : Fin m)
    (cut : ℕ) (hcut : cut≤2^(treeHeight learner a.lambda)) :
    GeneralPaperCatalogueEpochCDF.currentCDF learner (cacheAt (prepare a k Qv weights Bc Br) a k epochIndex) Qv weights Bc Br
      (GeneralPaperTreeLaw.law k (node learner (treesAt (prepare a k Qv weights Bc Br) a k epochIndex) j)) count j cut=
      GeneralPaperOrderedVariation.prefixMass
        (fun i => probability (GeneralPaperCachedMassJoin.base k) (history learner (prepare a k Qv weights Bc Br) a k j)
          (epochIndex*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period+count)
          (code (Nat.two_pow_pos (treeHeight learner a.lambda)) i)) cut := by
  let c := cacheAt (prepare a k Qv weights Bc Br) a k epochIndex
  have hw : GeneralPaperCatalogueEpochMetadata.width learner c=2^(treeHeight learner a.lambda) :=
    GeneralPaperCatalogueTreeCache.width_node _ _ a k _ learner
  rw [GeneralPaperEpochLaw.current_cdf_identity (Nat.two_pow_pos (treeHeight learner a.lambda)) _
    (GeneralPaperCachedMassJoin.base_positive k)]
  have hin (i : ℕ) (hi : i<2^(treeHeight learner a.lambda)) :
      GeneralPaperTreeLaw.law k (node learner (treesAt (prepare a k Qv weights Bc Br) a k epochIndex) j) i=
        probability (GeneralPaperCachedMassJoin.base k) (history learner (prepare a k Qv weights Bc Br) a k j)
          (epochIndex*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
          (code (Nat.two_pow_pos (treeHeight learner a.lambda)) i) := by
    have hcode : code (Nat.two_pow_pos (treeHeight learner a.lambda)) i=(⟨i,hi⟩:Fin (2^(treeHeight learner a.lambda))) :=
      GeneralPaperGeometricVariation.code_valid _ (⟨i,hi⟩:Fin (2^(treeHeight learner a.lambda)))
    rw [hcode]
    exact node_law learner a k Qv weights Bc Br epochIndex he j ⟨i,hi⟩
  have hp := funext (power_global learner a k Qv weights Bc Br epochIndex count hc j)
  unfold GeneralPaperCatalogueEpochCDF.currentCDF
  rw [hp]
  change GeneralPaperCDFReweighting.reweightedCDF _ _ (GeneralPaperCatalogueEpochMetadata.width learner c-1) cut=_
  rw [hw]
  unfold GeneralPaperCDFReweighting.reweightedCDF GeneralPaperCDFReweighting.weightedPrefix GeneralPaperOrderedVariation.prefixMass
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    dsimp only
    rw [hin i ((Finset.mem_range.mp hi).trans_le hcut)]
  · apply Finset.sum_congr rfl
    intro i hi
    dsimp only
    have hi' : i<2^(treeHeight learner a.lambda) := by
      have := Finset.mem_range.mp hi
      have := Nat.two_pow_pos (treeHeight learner a.lambda)
      omega
    rw [hin i hi']

end Blotto.GeneralPaperCatalogueGlobalCDF
