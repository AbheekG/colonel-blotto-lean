import Blotto.GeneralPaperStoredRejectionWork

/-! The actual sampler-root rejection price includes one actual Boolean
child load and the complete stored first-success computation. Native
constructor returns derive all owner/capacity premises internally. -/
namespace Blotto.GeneralPaperStoredSamplerRejectionWork
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperStoredReadContext (Context)
open GeneralPaperStoredChildRead (Child)
open GeneralPaperEqualRejectionTraceMeasure
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def entryBound (model : RationalCostModel) (A : ℕ) : ℕ :=
  GeneralPaperStoredReferenceReadWork.readBound model A A + 256 * (A + 1)

def expectedBound (model : RationalCostModel) (A w r count : ℕ) : ℕ :=
  2 * GeneralPaperStoredRejectionWork.perAttempt model A w r count + entryBound model A

theorem work (model : RationalCostModel) (S A start : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (ctx : Context model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A sampler)
      (GeneralPaperSamplerRecordCursor.expected model S A sampler start) installed)
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference)
    (cap : ℕ) (tape : ℕ → List Bool) :
    (GeneralPaperStoredSamplerRejection.run model A installed cap tape).work ≤
      cap * GeneralPaperStoredRejectionWork.perAttempt model A sampler.prepared.rangeBits
        (GeneralPaperPositiveSegmentCompaction.count l) sampler.categorical.rows.length + entryBound model A := by
  obtain ⟨fieldStart,hLoad,_,hRead,hHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperSamplerRecordCursor.schema model S A sampler) (GeneralPaperSamplerRecordCursor.child model S A sampler)
    GeneralPaperSamplerRecordCursor.fields ctx.contract.2.1 hRoot ⟨1,by decide⟩
  let child := GeneralPaperSamplerRecordCursor.child model S A sampler .boolean fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hReject := GeneralPaperStoredRejectionWork.work model S A start fieldStart _ _ loaded
    (GeneralPaperStoredReadContext.atRoot ctx child.root.reference) sampler.categorical hRead hHeaders rfl cap tape
  have hLoadWork := GeneralPaperStoredRecordReadWork.work model S A start start 64 _ _ installed ctx
    (GeneralPaperSamplerRecordCursor.schema model S A sampler) (GeneralPaperSamplerRecordCursor.child model S A sampler)
    GeneralPaperSamplerRecordCursor.fields ctx.contract.2.1 (fun _ hh => hh) hRoot ⟨1,by decide⟩
  change (GeneralPaperStoredChildRead.load model A installed 0 1).1 = some (⟨A,loaded⟩ : Child) at hLoad
  change (GeneralPaperStoredChildRead.load model A installed 0 1).2 ≤ _ at hLoadWork
  rw [(GeneralPaperStoredSamplerRejection.trace model A installed loaded cap tape hLoad).2.2]
  unfold entryBound
  omega

theorem expected_work (model : RationalCostModel) (S A start K : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (ctx : Context model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A sampler)
      (GeneralPaperSamplerRecordCursor.expected model S A sampler start) installed)
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference) :
    (∫⁻ trace, ((GeneralPaperStoredRejectionTrace.observed model A installed sampler.prepared.D K trace).work : ℝ≥0∞)
      ∂(law sampler.prepared.D K (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) : Measure (Trace sampler.prepared.D K))) ≤
      (expectedBound model A sampler.prepared.rangeBits (GeneralPaperPositiveSegmentCompaction.count l) sampler.categorical.rows.length : ℝ≥0∞) := by
  let B := GeneralPaperStoredRejectionWork.perAttempt model A sampler.prepared.rangeBits (GeneralPaperPositiveSegmentCompaction.count l) sampler.categorical.rows.length
  -- Integrating the entry once retains its exact constant allowance.
  have hPoint (trace : Trace sampler.prepared.D K) :
      (GeneralPaperStoredRejectionTrace.observed model A installed sampler.prepared.D K trace).work ≤
        (trace.1 + 1) * B + entryBound model A := work model S A start installed sampler ctx hRoot _ _
  calc
    _ ≤ ∫⁻ trace, (((trace.1 + 1) * B + entryBound model A : ℕ) : ℝ≥0∞)
        ∂(law sampler.prepared.D K (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) : Measure (Trace sampler.prepared.D K)) :=
      lintegral_mono (fun trace => (show ((GeneralPaperStoredRejectionTrace.observed model A installed sampler.prepared.D K trace).work : ℝ≥0∞) ≤
        (((trace.1 + 1) * B + entryBound model A : ℕ) : ℝ≥0∞) by exact_mod_cast hPoint trace))
    _ = (∫⁻ trace, (((trace.1 + 1) * B : ℕ) : ℝ≥0∞)
        ∂(law sampler.prepared.D K (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) : Measure (Trace sampler.prepared.D K))) + entryBound model A := by
      simp only [Nat.cast_add]
      rw [lintegral_add_left (measurable_of_countable _)]
      simp only [lintegral_const,measure_univ,mul_one]
    _ = ENNReal.ofReal ((B : ℝ) / (UniformNatRejection.acceptance sampler.prepared.D : ℝ)) + entryBound model A := by
      rw [GeneralPaperEqualBooleanTraceCost.charge_integral sampler.prepared.D K B (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared)]
    _ ≤ ((2 * B : ℕ) : ℝ≥0∞) + entryBound model A := by
      refine add_le_add ?_ le_rfl
      rw [← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      have ha := UniformNatRejection.acceptance_bounds sampler.prepared.D (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared)
      have hp : (0 : ℝ) < UniformNatRejection.acceptance sampler.prepared.D := by linarith only [ha.1]
      apply (div_le_iff₀ hp).mpr
      push_cast
      nlinarith only [ha.1,(Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
    _ = _ := by simp only [expectedBound,B,Nat.cast_add]

theorem native_expected {n : ℕ} (bits : Bool) (model : RationalCostModel) (W S k K : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (returned : Installed (GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget).address)
    (hReturn : (GeneralPaperCountedSamplerInstallation.build model S
      (GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget)).values = some returned) :
    let sampler := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
    (∫⁻ trace, ((GeneralPaperStoredRejectionTrace.observed model sampler.address returned sampler.prepared.D K trace).work : ℝ≥0∞)
      ∂(law sampler.prepared.D K (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) : Measure (Trace sampler.prepared.D K))) ≤
      (expectedBound model sampler.address sampler.prepared.rangeBits (GeneralPaperPositiveSegmentCompaction.count (GeneralPaperEqualFiniteKernel.lottery
        (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv) small)) sampler.categorical.rows.length : ℝ≥0∞) := by
  dsimp only
  let sampler := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
  obtain ⟨hA,hCap⟩ := GeneralPaperStoredNativeConstruction.native_bounds bits model W S k values v hv small budget
  obtain ⟨actual,hActual,_,_,hRoot,_⟩ := GeneralPaperCountedSamplerInstallation.build_source model S sampler hA hCap
  have hEq : actual = returned := Option.some.inj (hActual.symm.trans hReturn)
  subst actual
  exact expected_work model S sampler.address 0 K returned sampler
    (GeneralPaperStoredReadContext.native_return bits model W S k values v hv small budget returned hReturn) hRoot

end Blotto.GeneralPaperStoredSamplerRejectionWork
