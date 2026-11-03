import Blotto.GeneralPaperFirstStoredDominantContract

/-! The unchanged measured stored-memory constructor accepts the corrected
selected source. It returns actual installed fields and the same draw law;
all capacity and work premises are derived from that source. -/
namespace Blotto.GeneralPaperFirstStoredConstruction
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperStoredSelectedConstruction (run recast Contract)
open GeneralPaperCompleteSelectedPreparationWork (bound)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem source {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget) :
    ∃ returned : Installed a.address,(run model S a).1 = some returned ∧ returned.work = (run model S a).2 ∧
      Contract model a.address returned a.branch := by
  rcases a with ⟨branch,A,hAddress⟩
  cases branch with
  | dominant chosen heavy row correct =>
    let a : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget :=
      ⟨.dominant chosen heavy row correct,A,hAddress⟩
    obtain ⟨returned,hReturn,_,hWork,hDraw⟩ := GeneralPaperFirstStoredDominantContract.constructed model W S k values v hv budget a chosen heavy row correct rfl
    refine ⟨returned,?_,hWork,hDraw⟩
    simpa only [run,a] using hReturn
  | grouped small sampler hK hB =>
    dsimp only [GeneralPaperEqualSelectedSampler.baseReference] at hAddress
    subst A
    let a : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget :=
      ⟨.grouped small sampler hK hB,sampler.address + 1,rfl⟩
    have hI := GeneralPaperEqualFirstMeasuredLayout.inner_capacity model W S k values v hv budget a
    have hT := GeneralPaperEqualFirstMeasuredLayout.total_capacity model W S k values v hv budget a
    obtain ⟨returned,hReturn,_,hWork,hDraw⟩ := GeneralPaperStoredGroupedOuterConstruction.source model S sampler hI hT
    refine ⟨returned,?_,hWork,hDraw⟩
    simp only [run,hReturn,Option.map_some,recast]

theorem every_returned {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget)
    (returned : Installed a.address) (hReturn : (run model S a).1 = some returned) :
    Contract model a.address returned a.branch := by
  obtain ⟨actual,hActual,_,hContract⟩ := GeneralPaperFirstStoredConstruction.source model W S k values v hv budget a
  have hEq : actual = returned := Option.some.inj (hActual.symm.trans hReturn)
  rw [← hEq]
  exact hContract

theorem marker {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget)
    (returned : Installed a.address) (hReturn : (GeneralPaperStoredSelectedConstruction.run model S a).1 = some returned) :
    (GeneralPaperStoredOuterMarker.read model a.address returned).1 = some (GeneralPaperStoredOuterMarker.branchTag a.branch) := by
  rcases a with ⟨branch,A,hAddress⟩
  cases branch with
  | dominant chosen heavy row correct =>
    let a : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget :=
      ⟨.dominant chosen heavy row correct,A,hAddress⟩
    obtain ⟨hA,_,hCap⟩ := GeneralPaperFirstStoredDominantContract.bounds model W S k values v hv budget a chosen heavy row correct rfl
    exact GeneralPaperStoredOuterMarker.dominant_return model S A chosen.val row hA hCap returned hReturn
  | grouped small sampler hK hB =>
    dsimp only [GeneralPaperEqualSelectedSampler.baseReference] at hAddress
    subst A
    let a : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget :=
      ⟨.grouped small sampler hK hB,sampler.address + 1,rfl⟩
    have hCap := GeneralPaperEqualFirstMeasuredLayout.total_capacity model W S k values v hv budget a
    have hActual : (GeneralPaperStoredGroupedOuterConstruction.run model S sampler).values = some returned := by
      change Option.map (fun value : Installed (sampler.address + 1) => value)
        (GeneralPaperStoredGroupedOuterConstruction.run model S sampler).values = some returned at hReturn
      simpa using hReturn
    exact GeneralPaperStoredOuterMarker.grouped_return model S sampler hCap returned hActual


theorem refines {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget)
    (returned : Installed a.address) (hReturn : (run model S a).1=some returned) :
    GeneralPaperStoredSelectedDraw.Refines model a.address returned a.branch :=
  GeneralPaperStoredSelectedDraw.from_contract model a.address returned a.branch
    (every_returned model W S k values v hv budget a returned hReturn)
    (marker model W S k values v hv budget a returned hReturn)
theorem work {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget) :
    (GeneralPaperStoredSelectedConstruction.run model S source).2 ≤ bound model S source := by
  have hInnerCap := GeneralPaperEqualFirstMeasuredLayout.inner_capacity model W S k values v hv budget source
  have hOuterCap := GeneralPaperEqualFirstMeasuredLayout.total_capacity model W S k values v hv budget source
  have hWidths := GeneralPaperEqualMeasuredLayout.widths_positive source
  cases source with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy row correct =>
      change (GeneralPaperStoredDominantOuterConstruction.run model S A chosen.val row).work ≤ _
      exact GeneralPaperCompleteOuterPreparationWork.dominant_work model S A chosen.val row hWidths.2 hInnerCap hOuterCap
    | grouped small sampler hK hB =>
      dsimp only [GeneralPaperEqualSelectedSampler.baseReference] at hAddress
      subst A
      change (GeneralPaperStoredGroupedOuterConstruction.run model S sampler).work ≤ _
      exact GeneralPaperCompleteOuterPreparationWork.grouped_work model S sampler hInnerCap hOuterCap

theorem returned_work {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget)
    (returned : Installed source.address) (hReturn : (GeneralPaperStoredSelectedConstruction.run model S source).1 = some returned) :
    returned.work ≤ bound model S source := by
  obtain ⟨actual,hActual,hWork,_⟩ := GeneralPaperFirstStoredConstruction.source model W S k values v hv budget source
  have hSame : actual = returned := Option.some.inj (hActual.symm.trans hReturn)
  rw [← hSame,hWork]
  exact work model W S k values v hv budget source

theorem constructed {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget) :
    ∃ returned : Installed source.address,(GeneralPaperStoredSelectedConstruction.run model S source).1 = some returned ∧
      returned.work = (GeneralPaperStoredSelectedConstruction.run model S source).2 ∧ returned.work ≤ bound model S source ∧
      GeneralPaperStoredSelectedConstruction.Contract model source.address returned source.branch := by
  obtain ⟨returned,hReturn,hWork,hContract⟩ := GeneralPaperFirstStoredConstruction.source model W S k values v hv budget source
  exact ⟨returned,hReturn,hWork,returned_work model W S k values v hv budget source returned hReturn,hContract⟩


end Blotto.GeneralPaperFirstStoredConstruction
