import Blotto.GeneralPaperDirectoryPrefixLifetime

/-! Native selected write-prefix observers use the executed inner cursor,
count expansion and outer pointer encodings. Every prefix has finite RAM
ownership within the selected description, independently of write depth. -/
namespace Blotto.GeneralPaperSelectedInstallationPrefixes
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEqualMeasuredLayout (innerWidth)
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperUnifiedFieldValue (Value Memory encode)
open GeneralPaperPayloadMemoryOwnership (Bounded)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def innerInstalled {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : Installed (innerWidth source) :=
  GeneralPaperHeaderCountInstallation.finish model S (innerWidth source)
    (GeneralPaperSelectedCursorLifetime.parsed model S source).work
    (GeneralPaperSelectedTemporaryOwners.directory model S source)

def innerRun {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) :
    GeneralPaperUnifiedMatrixInstallation.Result (innerWidth source) :=
  match source with
  | ⟨.dominant chosen heavy row correct,A,hAddress⟩ =>
    GeneralPaperStoredDominantInstallation.run model S A chosen.val row
      (GeneralPaperEqualMeasuredLayout.run model S
        (⟨.dominant chosen heavy row correct,A,hAddress⟩ : Sampler v k budget)).inner
  | ⟨.grouped small sampler hK hB,A,hAddress⟩ =>
    GeneralPaperCountedSamplerInstallation.run model S sampler.address sampler
      (GeneralPaperEqualMeasuredLayout.run model S
        (⟨.grouped small sampler hK hB,A,hAddress⟩ : Sampler v k budget)).inner

theorem inner_return {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) :
    (innerRun model S source).values = some (innerInstalled model S source) ∧
      (innerRun model S source).remaining = [] ∧
      (innerRun model S source).work = (innerInstalled model S source).work := by
  have h := GeneralPaperSelectedCursorLifetime.same_return model S source
  cases source with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy row correct =>
      simp only [GeneralPaperSelectedCursorLifetime.parsed] at h
      simp only [innerRun,GeneralPaperStoredDominantInstallation.run,innerInstalled,
        GeneralPaperSelectedCursorLifetime.parsed,innerWidth,h.1,h.2,and_self]
    | grouped small sampler hK hB =>
      simp only [GeneralPaperSelectedCursorLifetime.parsed] at h
      simp only [innerRun,GeneralPaperCountedSamplerInstallation.run,innerInstalled,
        GeneralPaperSelectedCursorLifetime.parsed,innerWidth,h.1,h.2,and_self]

def tag {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (source : Sampler v k budget) : ℕ :=
  match source.branch with
  | .dominant _ _ _ _ => 0
  | .grouped _ _ _ _ => 1

def outerDirectory {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) :=
  GeneralPaperOuterAttachmentLifetime.directory model S (innerWidth source) source.address
    (GeneralPaperEqualOuterFieldLayout.canonical source.address (GeneralPaperEqualMeasuredLayout.run model S source).boundary)
    (innerInstalled model S source) (tag source)

def memory {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) (outer scalars : Bool) (depth : ℕ) : Memory :=
  if outer then
    GeneralPaperDirectoryPrefixLifetime.memory model S source.address (outerDirectory model S source)
      (innerInstalled model S source).memory scalars depth
  else
    GeneralPaperDirectoryPrefixLifetime.memory model S (innerWidth source)
      (GeneralPaperHeaderCountDirectory.prepare model S (innerWidth source)
        (GeneralPaperSelectedTemporaryOwners.directory model S source)).1
      (GeneralPaperPayloadMemory.empty Value) scalars depth

theorem inner_bounded {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) :
    Bounded encode (innerInstalled model S source).memory
      (GeneralPaperEqualMeasuredLayout.inner model S source).sizes.sum :=
  GeneralPaperUnifiedInstallationOwnership.counted_install model S (innerWidth source) 0 _
    (GeneralPaperEqualMeasuredLayout.inner model S source) (GeneralPaperSelectedTemporaryOwners.directory model S source)
    (GeneralPaperSelectedTemporaryOwners.directory_safe model S source)
    (GeneralPaperSelectedInstallationLifetime.directory_covered model S source)

theorem bounded {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) (outer scalars : Bool) (depth : ℕ) :
    Bounded encode (memory model S source outer scalars depth) (GeneralPaperEqualSelectedDescription.footprint source) := by
  have hArea : (GeneralPaperEqualMeasuredLayout.inner model S source).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S source.address).sizes.sum =
      GeneralPaperEqualSelectedDescription.footprint source := by
    rw [GeneralPaperEqualMeasuredLayout.inner,GeneralPaperEqualMeasuredSelectedPlan.branch_sum,
      GeneralPaperEqualMeasuredSelectedPlan.header_sum]
    rfl
  cases outer with
  | false =>
    exact GeneralPaperPayloadMemoryOwnership.mono encode _ _ _
      (GeneralPaperDirectoryPrefixLifetime.counted_prefix model S (innerWidth source) 0
        (GeneralPaperEqualMeasuredLayout.inner model S source) (GeneralPaperSelectedTemporaryOwners.directory model S source)
        (GeneralPaperSelectedTemporaryOwners.directory_safe model S source)
        (GeneralPaperSelectedInstallationLifetime.directory_covered model S source) scalars depth) (by omega)
  | true =>
    rw [← hArea]
    exact GeneralPaperDirectoryPrefixLifetime.prefix_bounded model S source.address
      (GeneralPaperEqualMeasuredLayout.run model S source).boundary _
      (GeneralPaperEqualMeasuredSelectedPlan.header model S source.address) (outerDirectory model S source)
      (innerInstalled model S source).memory (inner_bounded model S source)
      (GeneralPaperStoredOuterDirectory.safe model S source.address _ _ _)
      (GeneralPaperStoredOuterDirectory.covered model S source.address _ _ _) scalars depth

end Blotto.GeneralPaperSelectedInstallationPrefixes
