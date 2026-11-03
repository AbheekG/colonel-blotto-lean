import Blotto.GeneralPaperStoredReadWorkRates

/-! Instantiate read-work growth on the actual initialized/copied input
domain. The retained draw address is derived from its actual selected
return. Draw logarithms omit the accuracy input's encoding length. -/
namespace Blotto.GeneralPaperStoredNativeReadRates
open GeneralPaperEqualInputDomain (Input)
open GeneralPaperUniformResourceGrowth
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def drawLog {model : RationalCostModel} (p : Input model) : ℕ :=
  GeneralPaperEqualBitDrawRates.log p.n p.k (rationalWordWidth p.budget)

def scale {model : RationalCostModel} (p : Input model) : ℕ := p.n + rationalWordWidth p.budget + 1

theorem log_positive {model : RationalCostModel} (p : Input model) : 1 ≤ drawLog p := by
  unfold drawLog GeneralPaperEqualBitDrawRates.log
  omega

theorem address_tight (model : RationalCostModel) (A K : ℕ) :
    Tight (GeneralPaperStoredSelectedPipeline.width model A K) (drawLog (model := model)) := by
  refine ⟨3,fun p => ?_⟩
  have h := GeneralPaperEqualSelectedSampler.address_bound (GeneralPaperEqualCopiedPipeline.run model A K p).1
  have hL := log_positive p
  change (GeneralPaperEqualCopiedPipeline.run model A K p).1.address ≤ 3 * drawLog p
  change (GeneralPaperEqualCopiedPipeline.run model A K p).1.address ≤ 2 * drawLog p + 1 at h
  omega

theorem reference_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (A K : ℕ) :
    Polylog (fun p : Input model => GeneralPaperStoredReferenceReadWork.readBound model
      (GeneralPaperStoredSelectedPipeline.width model A K p) (GeneralPaperStoredSelectedPipeline.width model A K p)) drawLog :=
  GeneralPaperStoredReadWorkRates.reference_rate model hFast _ _ log_positive (address_tight model A K)

theorem dominant_emission_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (A K : ℕ) :
    Bound (fun p : Input model => GeneralPaperStoredDominantEmissionWork.vertexBound model
      (GeneralPaperStoredSelectedPipeline.width model A K p) p.n (rationalWordWidth p.budget)) scale drawLog := by
  have hn : Bound (fun p : Input model => p.n) scale drawLog := pointwise _ _ _ 1 (fun p => by unfold scale; omega)
  have hb : Bound (fun p : Input model => rationalWordWidth p.budget) scale drawLog := pointwise _ _ _ 1 (fun p => by unfold scale; omega)
  exact GeneralPaperStoredReadWorkRates.dominant_vertex_rate model hFast _ _ _ scale drawLog log_positive
    (fun p => by unfold scale; omega) (address_tight model A K) hn hb

theorem dominant_component {model : RationalCostModel} (A K S : ℕ) (p : Input model)
    (chosen : Fin p.n)
    (heavy : 1 / 2 ≤ (GeneralPaperEqualNativeSampler.rounded true model (GeneralPaperEqualInputDomain.word K p) p.k p.values p.selector p.correct).weight chosen)
    (row : RationalResourceArray p.n) (correct : row.realAllocation = PureBoundaryEquilibria.vertex (p.budget : ℝ) chosen)
    (hBranch : (GeneralPaperEqualCopiedPipeline.run model A K p).1.branch = .dominant chosen heavy row correct)
    (installed : GeneralPaperUnifiedDirectoryInstallation.Installed (GeneralPaperStoredSelectedPipeline.width model A K p))
    (hContract : GeneralPaperHeaderCountInstallation.Contract model (GeneralPaperStoredSelectedPipeline.width model A K p) installed
      (GeneralPaperStoredDominantCursor.expected model S (GeneralPaperStoredSelectedPipeline.width model A K p) chosen.val row 0))
    (hRoot : installed.root = (GeneralPaperStoredDominantCursor.expected model S (GeneralPaperStoredSelectedPipeline.width model A K p) chosen.val row 0).root.reference) :
    (GeneralPaperStoredDominantEmission.run model (GeneralPaperStoredSelectedPipeline.width model A K p) installed).work ≤
      GeneralPaperStoredDominantEmissionWork.vertexBound model (GeneralPaperStoredSelectedPipeline.width model A K p) p.n (rationalWordWidth p.budget) := by
  obtain ⟨hA,hCap,_⟩ := GeneralPaperStoredDominantOuterContract.bounds model (GeneralPaperEqualInputDomain.word K p) S p.k
    p.values p.selector p.correct p.budget (GeneralPaperEqualCopiedPipeline.run model A K p).1 chosen heavy row correct hBranch
  exact (GeneralPaperStoredDominantEmissionWork.work model S _ 0 chosen.val installed row hContract hRoot hA
    (by simpa only [Nat.zero_add,GeneralPaperStoredSelectedPipeline.width] using hCap)).trans
      (GeneralPaperStoredDominantEmissionWork.vertex_bound model _ p.budget chosen row correct)

end Blotto.GeneralPaperStoredNativeReadRates
