import Blotto.GeneralPaperStoredMidpointWork
import Blotto.GeneralPaperStoredSamplerMidpoint

/-! Complete midpoint work at the actual sampler root includes its one
prepared-child load. Every native constructor return derives readback,
capacity and scalar-owner premises in the same installed memory. -/
namespace Blotto.GeneralPaperStoredSamplerMidpointWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperStoredReadContext (Context)
open GeneralPaperStoredChildRead (Child)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def bound (model : RationalCostModel) (A : ℕ) (prepared : GeneralPaperEqualPreparedCache.Prepared G l) : ℕ :=
  GeneralPaperStoredMidpointWork.bound model A prepared +
    GeneralPaperStoredReferenceReadWork.readBound model A A + 256 * (A + 1)

def majorant (model : RationalCostModel) (A P K : ℕ) : ℕ :=
  GeneralPaperStoredPreparedReadWork.controlsMajorant model A P +
    GeneralPaperStoredFreshDecoderWork.bound model A K +
    24 * model.rat (1 + 2 * GeneralPaperCachedMidpointAssembly.height K) +
    96 * A + 96 + 384 * (A + 1) + GeneralPaperStoredReferenceReadWork.readBound model A A

theorem bound_le (model : RationalCostModel) (A P : ℕ) (prepared : GeneralPaperEqualPreparedCache.Prepared G l)
    (hControl : ∀ x ∈ GeneralPaperPreparedRecordCursor.controls prepared,GeneralPaperEncodedScalarStorage.natBits x ≤ P) :
    bound model A prepared ≤ majorant model A P prepared.midpointBits := by
  have hControls := GeneralPaperStoredPreparedReadWork.controls_bound model A P prepared hControl
  unfold bound majorant GeneralPaperStoredMidpointWork.bound
  omega

theorem native_majorant {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let source := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
    bound model source.address source.prepared ≤
      majorant model source.address (3670016 * GeneralPaperEqualNativeRetainedStorage.short n k + 3) (k + 5) := by
  dsimp only
  exact bound_le model _ _ _ (GeneralPaperEqualNativeDrawRepresentation.native_controls bits model W k values v hv small budget)

theorem work (model : RationalCostModel) (S A start : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (ctx : Context model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A sampler)
      (GeneralPaperSamplerRecordCursor.expected model S A sampler start) installed)
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference)
    (fresh : Fin sampler.prepared.midpointBits → Bool) :
    (GeneralPaperStoredSamplerMidpoint.run model A installed GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work ≤
      bound model A sampler.prepared := by
  obtain ⟨fieldStart,hLoad,_,hRead,hHeaders,hCells⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperSamplerRecordCursor.schema model S A sampler) (GeneralPaperSamplerRecordCursor.child model S A sampler)
    GeneralPaperSamplerRecordCursor.fields ctx.contract.2.1 hRoot ⟨0,by decide⟩
  let child := GeneralPaperSamplerRecordCursor.child model S A sampler .prepared fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hMidpoint := GeneralPaperStoredMidpointWork.work model S A start fieldStart _ _ loaded
    (GeneralPaperStoredReadContext.atRoot ctx child.root.reference) sampler.prepared hRead hHeaders hCells rfl fresh
  have hLoadWork := GeneralPaperStoredRecordReadWork.work model S A start start 64 _ _ installed ctx
    (GeneralPaperSamplerRecordCursor.schema model S A sampler) (GeneralPaperSamplerRecordCursor.child model S A sampler)
    GeneralPaperSamplerRecordCursor.fields ctx.contract.2.1 (fun _ hh => hh) hRoot ⟨0,by decide⟩
  change (GeneralPaperStoredChildRead.load model A installed 0 0).1 = some (⟨A,loaded⟩ : Child) at hLoad
  change (GeneralPaperStoredChildRead.load model A installed 0 0).2 ≤ _ at hLoadWork
  rw [(GeneralPaperStoredSamplerMidpoint.trace model A installed loaded GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh) hLoad).2.2.2]
  unfold bound
  omega

theorem native_work {n : ℕ} (bits : Bool) (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (returned : Installed (GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget).address)
    (hReturn : (GeneralPaperCountedSamplerInstallation.build model S
      (GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget)).values = some returned)
    (fresh : Fin (GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget).prepared.midpointBits → Bool) :
    let source := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
    (GeneralPaperStoredSamplerMidpoint.run model source.address returned GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work ≤
      bound model source.address source.prepared := by
  dsimp only
  let source := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
  have ctx := GeneralPaperStoredReadContext.native_return bits model W S k values v hv small budget returned hReturn
  obtain ⟨hA,hCap⟩ := GeneralPaperStoredNativeConstruction.native_bounds bits model W S k values v hv small budget
  obtain ⟨output,hBuilt,_,_,hRoot,_⟩ := GeneralPaperCountedSamplerInstallation.build_source model S source hA hCap
  have hEq : output = returned := Option.some.inj (hBuilt.symm.trans hReturn)
  subst output
  exact work model S source.address 0 returned source ctx hRoot fresh

end Blotto.GeneralPaperStoredSamplerMidpointWork
