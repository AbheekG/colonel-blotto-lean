import Blotto.GeneralPaperStoredPreparationCallerLifetime

/-! Every actual word/scalar write prefix of a directory extension has
finite resident ownership paid by the incoming memory and measured area.
The complete extension temporary window coexists with each prefix. -/
namespace Blotto.GeneralPaperDirectoryPrefixLifetime
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperFieldDirectorySafety (Safe)
open GeneralPaperFieldDirectoryPartition (Covered)
open GeneralPaperMeasuredBlockPlan (Plan)
open GeneralPaperScalarFieldCursor (Cell)
open GeneralPaperUnifiedFieldValue (Memory Value encode)
open GeneralPaperPayloadMemoryOwnership (Bounded payload cellSize)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def memory (model : RationalCostModel) (S A : ℕ) (directory : Directory A) (incoming : Memory) (scalars : Bool) (depth : ℕ) : Memory :=
  let words := (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries
  let first := (GeneralPaperUnifiedFieldMemory.liftWords S A words).1
  let second := (GeneralPaperUnifiedFieldMemory.liftScalars S A (directory.cells.map Cell.entry)).1
  if scalars then
    (GeneralPaperPayloadMemory.install S A encode (GeneralPaperPayloadMemory.install S A encode incoming first).1 (second.take depth)).1
  else (GeneralPaperPayloadMemory.install S A encode incoming (first.take depth)).1

theorem prefix_bounded (model : RationalCostModel) (S A start B : ℕ) (plan : Plan) (directory : Directory A)
    (incoming : Memory) (hIncoming : Bounded encode incoming B)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (scalars : Bool) (depth : ℕ) : Bounded encode (memory model S A directory incoming scalars depth) (B + plan.sizes.sum) := by
  have hArea := GeneralPaperFieldDirectorySeparation.joint_area model S A start plan directory hSafe hCovered
  have hParameters : (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries.length * A +
      payload GeneralPaperRetainedScalarValue.encode (directory.cells.map Cell.entry) ≤ plan.sizes.sum := by
    simp only [GeneralPaperReferenceRegionProgram.count,GeneralPaperReferenceHeaderSlotArea.slots,
      payload,List.map_map,Cell.entry,Function.comp_def] at hArea ⊢
    nlinarith only [hArea]
  cases scalars with
  | false =>
    have h := GeneralPaperUnifiedInstallationOwnership.word_prefix S A B
      (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries incoming hIncoming depth
    exact GeneralPaperPayloadMemoryOwnership.mono encode _ _ _ h (by omega)
  | true =>
    have h := GeneralPaperUnifiedInstallationOwnership.scalar_prefix S A B
      (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries (directory.cells.map Cell.entry) incoming hIncoming depth
    exact GeneralPaperPayloadMemoryOwnership.mono encode _ _ _ h (by change B + _ + payload _ _ ≤ _; omega)

theorem counted_prefix (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (directory : Directory A)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (scalars : Bool) (depth : ℕ) :
    Bounded encode (memory model S A (GeneralPaperHeaderCountDirectory.prepare model S A directory).1
      (GeneralPaperPayloadMemory.empty Value) scalars depth) plan.sizes.sum := by
  simpa only [Nat.zero_add,GeneralPaperHeaderCountDirectory.data] using prefix_bounded model S A start 0 plan _ (GeneralPaperPayloadMemory.empty Value)
    (GeneralPaperPayloadMemoryOwnership.empty_bounded encode) (GeneralPaperHeaderCountDirectory.safe _ directory hSafe)
    (GeneralPaperHeaderCountDirectory.covered _ directory hCovered) scalars depth

theorem prefix_coexistence (model : RationalCostModel) (S A start B : ℕ) (plan : Plan) (directory : Directory A)
    (incoming : Memory) (hIncoming : Bounded encode incoming B)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A)
    (scalars : Bool) (depth : ℕ) :
    ∃ keys : Finset ℕ,(∀ key,memory model S A directory incoming scalars depth key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys,cellSize encode (memory model S A directory incoming scalars depth) key) +
        GeneralPaperDirectoryExtensionLifetime.window model S A directory incoming ≤
      B + plan.sizes.sum + GeneralPaperDirectoryExtensionLifetime.profile model S A plan.sizes.sum := by
  obtain ⟨keys,hSupport,hResident⟩ := prefix_bounded model S A start B plan directory incoming hIncoming hSafe hCovered scalars depth
  exact ⟨keys,hSupport,Nat.add_le_add hResident
    (GeneralPaperDirectoryExtensionLifetime.window_bound model S A start plan directory incoming hSafe hCovered hPos hA hCap)⟩

theorem outer_prefix_coexistence (model : RationalCostModel) (S I A start prefixWork tag P B : ℕ)
    (inner : GeneralPaperUnifiedDirectoryInstallation.Installed I) (hIncoming : Bounded encode inner.memory B)
    (hA : 0 < A) (hI : I ≤ A) (hTag : tag < 2 ^ A)
    (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A)
    (hWork : (GeneralPaperStoredOuterAttachment.finish model S I A prefixWork (GeneralPaperEqualOuterFieldLayout.canonical A start) inner tag).work ≤ P)
    (scalars : Bool) (depth : ℕ) :
    let directory := GeneralPaperOuterAttachmentLifetime.directory model S I A (GeneralPaperEqualOuterFieldLayout.canonical A start) inner tag
    ∃ keys : Finset ℕ,(∀ key,memory model S A directory inner.memory scalars depth key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys,cellSize encode (memory model S A directory inner.memory scalars depth) key) +
        GeneralPaperOuterAttachmentLifetime.window model S I A prefixWork (GeneralPaperEqualOuterFieldLayout.canonical A start) inner tag ≤
      B + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum +
        GeneralPaperOuterAttachmentLifetime.profile model S A (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum P := by
  dsimp only
  obtain ⟨keys,hSupport,hResident⟩ := prefix_bounded model S A start B (GeneralPaperEqualMeasuredSelectedPlan.header model S A)
    (GeneralPaperOuterAttachmentLifetime.directory model S I A (GeneralPaperEqualOuterFieldLayout.canonical A start) inner tag)
    inner.memory hIncoming (GeneralPaperStoredOuterDirectory.safe model S A start _ _) (GeneralPaperStoredOuterDirectory.covered model S A start _ _)
    scalars depth
  exact ⟨keys,hSupport,Nat.add_le_add hResident
    (GeneralPaperOuterAttachmentLifetime.window_bound model S I A start prefixWork tag P inner hA hI hTag hCap hWork)⟩

end Blotto.GeneralPaperDirectoryPrefixLifetime
