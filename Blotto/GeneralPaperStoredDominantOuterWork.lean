import Blotto.GeneralPaperStoredGroupedOuterNativeWork

/-! Complete dominant outer drawing copies its counted vertex row in the
same extended memory. Native capacities and the one nonzero budget payload
are derived from the actual selected constructor and canonical vertex. -/
namespace Blotto.GeneralPaperStoredDominantOuterWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperEqualOuterFieldLayout
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def bound {n : ℕ} (model : RationalCostModel) (A : ℕ) (row : RationalResourceArray n) : ℕ :=
  GeneralPaperStoredDispatchLoadWork.dominantBound model A + GeneralPaperStoredDominantEmissionWork.bound model A row + 256 * (A + 1)

def vertexBound (model : RationalCostModel) (A n b : ℕ) : ℕ :=
  GeneralPaperStoredDispatchLoadWork.dominantBound model A + GeneralPaperStoredDominantEmissionWork.vertexBound model A n b + 256 * (A + 1)

theorem attached_work {n : ℕ} (model : RationalCostModel) (S A prefixWork chosen : ℕ) (row : RationalResourceArray n) (inner : Installed A)
    (hContract : Contract model A inner (GeneralPaperStoredDominantCursor.expected model S A chosen row 0))
    (hRoot : inner.root = (GeneralPaperStoredDominantCursor.expected model S A chosen row 0).root.reference)
    (hA : 0 < A) (hInnerCap : (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum < 2 ^ A)
    (hOuterCap : (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) :
    let outer := GeneralPaperStoredOuterAttachment.finish model S A A prefixWork
      (canonical A (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum) inner 0
    (GeneralPaperStoredDominantOuterDraw.run model A outer).work ≤ bound model A row := by
  dsimp only
  let plan := GeneralPaperStoredDominantCursor.plan model S A chosen row
  let fields := canonical A plan.sizes.sum
  let outer := GeneralPaperStoredOuterAttachment.finish model S A A prefixWork fields inner 0
  let loaded := GeneralPaperStoredScalarRead.atRoot outer inner.root
  have hSafe := (GeneralPaperStoredDominantCursor.success model S A 0 chosen row []).2.2.1
  have hNew := GeneralPaperStoredOuterAttachment.inner_contract model S A A prefixWork plan _ inner 0 hSafe hA hInnerCap hContract hA hOuterCap
  have hLoaded : Contract model A loaded (GeneralPaperStoredDominantCursor.expected model S A chosen row 0) := hNew
  have hEmit := GeneralPaperStoredDominantEmissionWork.work model S A 0 chosen loaded row hLoaded hRoot hA
    (by simpa only [Nat.zero_add] using hInnerCap)
  have hRead := GeneralPaperStoredOuterAttachment.outer_readback model S A A plan.sizes.sum prefixWork inner 0 hA hOuterCap
  have hCapacity := GeneralPaperStoredOuterReadWork.capacity model S A plan.sizes.sum hA hOuterCap
  have hLoadWork := GeneralPaperStoredDispatchLoadWork.dominant_work model A outer fields inner.root hRead rfl hCapacity.1
  have hLoad := GeneralPaperStoredDominantOuterDraw.attached_load model S A plan.sizes.sum prefixWork inner hA hOuterCap
  change (GeneralPaperStoredDominantOuterDraw.load model A outer).1 = some (⟨A,loaded⟩ : GeneralPaperStoredChildRead.Child) at hLoad
  change (GeneralPaperStoredDominantOuterDraw.run model A outer).work ≤ bound model A row
  simp only [GeneralPaperStoredDominantOuterDraw.run,hLoad]
  unfold bound
  omega

theorem every_returned_work {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (row : RationalResourceArray n)
    (hA : 0 < A) (hInnerCap : (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum < 2 ^ A)
    (hOuterCap : (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A)
    (returned : Installed A) (hReturn : (GeneralPaperStoredDominantOuterConstruction.run model S A chosen row).values = some returned) :
    (GeneralPaperStoredDominantOuterDraw.run model A returned).work ≤ bound model A row := by
  obtain ⟨inner,hInner,_,_,hRoot,hContract⟩ := GeneralPaperStoredDominantInstallation.source model S A 0 chosen row [] hA
    (by simpa only [Nat.zero_add] using hInnerCap)
  simp only [List.append_nil] at hInner
  have hInnerActual : (GeneralPaperStoredDominantInstallation.run model S A chosen row
      (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen row).inner).values = some inner := hInner
  have hBoundary : (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen row).boundary =
      (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum := GeneralPaperMeasuredTwoPoolLayout.boundary model S A A _ _
  have hPrice := attached_work model S A
    ((GeneralPaperStoredDominantOuterConstruction.layout model S A chosen row).work +
      (extract S A (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen row).outer).2)
    chosen row inner hContract hRoot hA hInnerCap hOuterCap
  simp only [GeneralPaperStoredDominantOuterConstruction.run,hInnerActual,GeneralPaperStoredDominantOuterConstruction.fields_source] at hReturn
  rw [← Option.some.inj hReturn]
  simpa only [hBoundary] using hPrice

theorem native_vertex {n : ℕ} (model : RationalCostModel) (W S k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ)
    (a : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (chosen : Fin n) (heavy : 1 / 2 ≤ (GeneralPaperEqualNativeSampler.rounded true model W k values v hv).weight chosen)
    (row : RationalResourceArray n) (correct : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hBranch : a.branch = .dominant chosen heavy row correct) (returned : Installed a.address)
    (hReturn : (GeneralPaperStoredDominantOuterConstruction.run model S a.address chosen.val row).values = some returned) :
    (GeneralPaperStoredDominantOuterDraw.run model a.address returned).work ≤ vertexBound model a.address n (rationalWordWidth budget) := by
  obtain ⟨hA,hInner,hOuter⟩ := GeneralPaperStoredDominantOuterContract.bounds model W S k values v hv budget a chosen heavy row correct hBranch
  have hWork := every_returned_work model S a.address chosen.val row hA hInner hOuter returned hReturn
  have hVertex := GeneralPaperStoredDominantEmissionWork.vertex_bound model a.address budget chosen row correct
  unfold bound at hWork
  unfold vertexBound
  omega

theorem vertex_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (A n b r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hA : Tight A L) (hn : Bound n r L) (hb : Bound b r L) :
    Bound (fun x => vertexBound model (A x) (n x) (b x)) r L := by
  have hAP := polylog_of_tight hA
  have hMeta := rate_mono (GeneralPaperStoredOuterWorkRates.dominant_rate model hFast A L hL hA) hr
  have hVertex := GeneralPaperStoredReadWorkRates.dominant_vertex_rate model hFast A n b r L hL hr hA hn hb
  unfold vertexBound
  fun_prop

end Blotto.GeneralPaperStoredDominantOuterWork
