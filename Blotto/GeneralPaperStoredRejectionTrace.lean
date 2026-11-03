import Blotto.GeneralPaperStoredSamplerRejection

/-! The already normalized fair terminal-trace measure observes the actual
stored sampler-root runner. Tape reconstruction and source objects below are
proof-only observers; none is an execution or stopping oracle. -/
namespace Blotto.GeneralPaperStoredRejectionTrace
open MeasureTheory
open scoped ENNReal
open GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperEqualRejectionTraceMeasure
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def rawBlocks (N : ℕ) (tape : ℕ → Fin (UniformNatRejection.width N) → Bool) : ℕ → List Bool := fun t => List.ofFn (tape t)

theorem blocks_eq (prepared : GeneralPaperEqualPreparedCache.Prepared G l)
    (tape : ℕ → Fin (UniformNatRejection.width prepared.D) → Bool) :
    GeneralPaperStoredBooleanRejection.blocks prepared tape = rawBlocks prepared.D tape := by
  funext t
  exact (List.ofFn_congr prepared.rangeBits_correct.symm (tape t)).symm

noncomputable def observed (model : RationalCostModel) (A : ℕ) (installed : Installed A) (N K : ℕ) (trace : Trace N K) :=
  GeneralPaperStoredSamplerRejection.run model A installed (trace.1 + 1)
    (rawBlocks N (GeneralPaperEqualBooleanTraceCost.tapeFor N K trace))

def Refines (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) (K : ℕ) : Prop :=
  ∀ trace : Trace sampler.prepared.D K,
    (observed model A installed sampler.prepared.D K trace).output =
      (GeneralPaperEqualBooleanTraceCost.observed sampler.categorical K trace).output.map Fin.val ∧
    (observed model A installed sampler.prepared.D K trace).reads =
      (GeneralPaperEqualBooleanTraceCost.observed sampler.categorical K trace).reads

theorem from_directory (model : RationalCostModel) (S A start : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hContract : Contract model A installed (GeneralPaperSamplerRecordCursor.expected model S A sampler start))
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference)
    (hA : 0 < A) (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A sampler).sizes.sum < 2 ^ A) (K : ℕ) :
    Refines model A installed sampler K := by
  intro trace
  let tape := GeneralPaperEqualBooleanTraceCost.tapeFor sampler.prepared.D K trace
  obtain ⟨_,hv,hr,_⟩ := GeneralPaperStoredSamplerRejection.source model S A start installed sampler hContract hRoot hA hCap (trace.1 + 1) tape
  rw [blocks_eq] at hv hr
  obtain ⟨hOld,hOldReads⟩ := GeneralPaperEqualBooleanRejection.data sampler.categorical (trace.1 + 1) tape
  refine ⟨?_,hr.trans hOldReads.symm⟩
  change _ = (GeneralPaperEqualBooleanRejection.run sampler.categorical (trace.1 + 1) tape).output.map Fin.val
  rw [hOld,Option.map_map]
  exact hv

theorem every_returned (model : RationalCostModel) (S : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hA : 0 < sampler.address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum < 2 ^ sampler.address)
    (returned : Installed sampler.address) (hReturn : (GeneralPaperCountedSamplerInstallation.build model S sampler).values = some returned) (K : ℕ) :
    Refines model sampler.address returned sampler K := by
  obtain ⟨output,hBuilt,_,_,hRoot,hContract⟩ := GeneralPaperCountedSamplerInstallation.build_source model S sampler hA hCap
  have hEq : output = returned := Option.some.inj (hBuilt.symm.trans hReturn)
  subst output
  exact from_directory model S sampler.address 0 returned sampler hContract hRoot hA (by simpa only [Nat.zero_add] using hCap) K

theorem completed_ae (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) (K : ℕ) (hRefines : Refines model A installed sampler K) :
    ∀ᵐ trace ∂(law sampler.prepared.D K (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) : Measure (Trace sampler.prepared.D K)),
      ∃ label, (observed model A installed sampler.prepared.D K trace).output = some label := by
  filter_upwards [GeneralPaperEqualBooleanTraceCost.completed_ae sampler.categorical K] with trace h
  obtain ⟨label,hLabel⟩ := h
  rw [(hRefines trace).1,hLabel,Option.map_some]
  exact ⟨label.val,rfl⟩

theorem expected_reads_exact (model : RationalCostModel) (A : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) (K : ℕ) (hRefines : Refines model A installed sampler K) :
    (∫⁻ trace, ((observed model A installed sampler.prepared.D K trace).reads : ℝ≥0∞)
      ∂(law sampler.prepared.D K (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) : Measure (Trace sampler.prepared.D K))) =
        ENNReal.ofReal ((UniformNatRejection.width sampler.prepared.D : ℝ) / (UniformNatRejection.acceptance sampler.prepared.D : ℝ)) := by
  calc
    _ = ∫⁻ trace, ((GeneralPaperEqualBooleanTraceCost.observed sampler.categorical K trace).reads : ℝ≥0∞)
        ∂(law sampler.prepared.D K (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) : Measure (Trace sampler.prepared.D K)) := by
      apply lintegral_congr_ae
      filter_upwards [] with trace
      rw [(hRefines trace).2]
    _ = _ := GeneralPaperEqualBooleanTraceCost.expected_reads_exact sampler.categorical K

end Blotto.GeneralPaperStoredRejectionTrace
