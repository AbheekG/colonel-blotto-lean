import Blotto.GeneralPaperDirectoryInstallationLifetime

/-! Native selected inner-directory installation discharges all complete
unified-installer lifetime premises from its actual cursor/layout owners.
The same count-initialized inner memory coexists with that window. Uniform
paper-input bounds cover both branches and arbitrary parent-width functions. -/
namespace Blotto.GeneralPaperSelectedInstallationLifetime
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEqualMeasuredLayout
open GeneralPaperPayloadMemoryOwnership (Bounded cellSize)
open GeneralPaperUnifiedFieldValue (Value encode)
open GeneralPaperEqualInputDomain
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem directory_covered {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) :
    GeneralPaperFieldDirectoryPartition.Covered
      (GeneralPaperMeasuredBlockLayout.run model S (innerWidth source) 0 (inner model S source)).1
      (GeneralPaperSelectedTemporaryOwners.directory model S source) := by
  cases source with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy row correct =>
      exact (GeneralPaperStoredDominantCursor.success model S A 0 chosen.val row []).2.2.2
    | grouped small sampler hK hB =>
      exact (GeneralPaperSamplerRecordCursor.success model S sampler.address 0 sampler []).2.2.2

def window {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  GeneralPaperDirectoryInstallationLifetime.window model S (innerWidth source)
    (GeneralPaperHeaderCountDirectory.prepare model S (innerWidth source)
      (GeneralPaperSelectedTemporaryOwners.directory model S source)).1 (GeneralPaperPayloadMemory.empty Value)

def bound {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  GeneralPaperDirectoryInstallationLifetime.profile model S (innerWidth source) (inner model S source).sizes.sum

theorem window_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    window model S source ≤ bound model S source := by
  have hWidths := widths_positive source
  exact GeneralPaperDirectoryInstallationLifetime.count_expanded_window model S (innerWidth source) 0 (inner model S source)
    (GeneralPaperSelectedTemporaryOwners.directory model S source) (GeneralPaperPayloadMemory.empty Value)
    (GeneralPaperSelectedTemporaryOwners.directory_safe model S source) (directory_covered model S source)
    (GeneralPaperSelectedTemporaryOwners.inner_good model S source).1 hWidths.1
    (by simpa only [Nat.zero_add] using inner_capacity model W S k values v hv budget source)

theorem inner_resident_coexistence {n : ℕ} (model : RationalCostModel) (W S k prefixWork : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    let output := GeneralPaperHeaderCountInstallation.finish model S (innerWidth source) prefixWork
      (GeneralPaperSelectedTemporaryOwners.directory model S source)
    ∃ keys : Finset ℕ,(∀ key,output.memory key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys,cellSize encode output.memory key) + window model S source ≤
        (inner model S source).sizes.sum + bound model S source := by
  have hWidths := widths_positive source
  have hSafe := GeneralPaperSelectedTemporaryOwners.directory_safe model S source
  have hCovered := directory_covered model S source
  have hExpandedSafe := GeneralPaperHeaderCountDirectory.safe _ _ hSafe
  have hExpandedCovered := GeneralPaperHeaderCountDirectory.covered _ _ hCovered
  have hCoexistence := GeneralPaperDirectoryInstallationLifetime.resident_coexistence model S (innerWidth source) 0 0
    (inner model S source) (GeneralPaperHeaderCountDirectory.expanded (GeneralPaperSelectedTemporaryOwners.directory model S source))
    (GeneralPaperPayloadMemory.empty Value) (GeneralPaperPayloadMemoryOwnership.empty_bounded encode)
    hExpandedSafe hExpandedCovered (GeneralPaperSelectedTemporaryOwners.inner_good model S source).1 hWidths.1
    (by simpa only [Nat.zero_add] using inner_capacity model W S k values v hv budget source)
  simpa only [GeneralPaperHeaderCountInstallation.finish,GeneralPaperHeaderCountDirectory.data,
    GeneralPaperStoredDirectoryExtension.install,GeneralPaperUnifiedDirectoryInstallation.install,window,bound,Nat.zero_add] using hCoexistence

theorem input_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (K : ℕ) (parent : Input model → ℕ) :
    Bound (fun p => bound model (word K p) (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1) ledger logarithm := by
  have hAddress := GeneralPaperSelectedPreparationInputRates.address_tight model K parent
  have hI : Tight (fun p : Input model => innerWidth (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1) logarithm := by
    obtain ⟨C,hC⟩ := hAddress
    exact ⟨C,fun p => (GeneralPaperCompleteSelectedPreparationWork.inner_width_le _).trans (hC p)⟩
  have hBi : Bound (fun p : Input model =>
      (inner model (word K p) (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1).sizes.sum) ledger logarithm := by
    apply dominated (GeneralPaperSelectedPreparationInputRates.description_rate model K parent)
    intro p
    dsimp only [GeneralPaperEqualMeasuredLayout.inner]
    rw [GeneralPaperEqualMeasuredSelectedPlan.branch_sum]
    unfold GeneralPaperEqualSelectedDescription.footprint
    dsimp only [GeneralPaperSelectedPreparationInputRates.source]
    omega
  have hLedger : Small (ledger (model := model)) logarithm := by
    refine ⟨1,fun p => ?_⟩
    unfold logarithm
    omega
  exact GeneralPaperDirectoryInstallationLifetime.profile_rate model hFast (word K)
    (fun p => innerWidth (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1)
    (fun p => (inner model (word K p) (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1).sizes.sum)
    ledger logarithm logarithm_positive ledger_positive (word_tight K model) hI hBi hLedger

theorem actual_input_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (K : ℕ) (parent : Input model → ℕ) :
    Bound (fun p => window model (word K p) (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1) ledger logarithm := by
  apply dominated (input_rate model hFast K parent)
  intro p
  exact window_bound model (word K p) (word K p) p.k p.values p.selector p.correct p.budget _

theorem paper_space (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (K : ℕ) (parent : Input model → ℕ) :
    ∃ C d : ℕ,∀ p : Input model,
      window model (word K p) (GeneralPaperEqualCopiedPipeline.run model (parent p) K p).1 ≤
        C * GeneralPaperEqualInputHeadline.inputSize p * (GeneralPaperEqualInputHeadline.paperLog p) ^ d :=
  GeneralPaperEqualInputHeadline.transfer_rate (actual_input_rate model hFast K parent)

end Blotto.GeneralPaperSelectedInstallationLifetime
