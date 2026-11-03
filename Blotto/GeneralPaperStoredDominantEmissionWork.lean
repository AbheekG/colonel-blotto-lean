import Blotto.GeneralPaperStoredRationalCollectionWork

/-! The complete actual dominant row emitter has an additive payload bound,
including its child load, count read, rational copies and one full array
materialization. Actual measured owners derive all count/index capacities. -/
namespace Blotto.GeneralPaperStoredDominantEmissionWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperStoredChildRead (Child)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperRetainedScalarValue (Scalar)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def bound {n : ℕ} (model : RationalCostModel) (A : ℕ) (row : RationalResourceArray n) : ℕ :=
  GeneralPaperStoredRationalCollectionWork.bound model A (GeneralPaperStoredDominantCursor.rowTable row) +
    64 * (n + 1) * A + GeneralPaperStoredReferenceReadWork.readBound model A A + 512 * (A + 1)

theorem work {n : ℕ} (model : RationalCostModel) (S A start chosen : ℕ) (installed : Installed A)
    (row : RationalResourceArray n)
    (hContract : Contract model A installed (GeneralPaperStoredDominantCursor.expected model S A chosen row start))
    (hRoot : installed.root = (GeneralPaperStoredDominantCursor.expected model S A chosen row start).root.reference)
    (hA : 0 < A) (hCap : start + (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum < 2 ^ A) :
    (GeneralPaperStoredDominantEmission.run model A installed).work ≤ bound model A row := by
  obtain ⟨fieldStart,hLoad,hPointer,hRead,hHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 32 installed
    (GeneralPaperStoredDominantCursor.schema model S A chosen row) (GeneralPaperStoredDominantCursor.child model S A chosen row)
    GeneralPaperStoredDominantCursor.fields hContract.2.1 hRoot ⟨0,by decide⟩
  let directory := GeneralPaperStoredDominantCursor.expected model S A chosen row start
  let child := GeneralPaperStoredDominantCursor.child model S A chosen row .row fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  change (GeneralPaperStoredChildRead.load model A installed 0 0).1 = some (⟨A,loaded⟩ : Child) at hLoad
  change (GeneralPaperMixedReferenceRegionProgram.read model A (GeneralPaperUnifiedFieldValue.referenceMemory installed.memory)
    installed.root 0 0).1 = some (⟨A,child.root.reference⟩ : GeneralPaperMixedReferenceMemory.Word) at hPointer
  have hChildContract : Contract model A loaded directory := hContract
  have hHeader := hHeaders _ (List.mem_singleton_self _)
  have hSafe := (GeneralPaperStoredDominantCursor.success model S A start chosen row []).2.2.1
  have hCaps := GeneralPaperReferenceLayoutInstallation.capacities model S A start
    (GeneralPaperStoredDominantCursor.plan model S A chosen row) directory.headers hSafe.2.1 hCap
  have hOwner := hCaps _ hHeader
  have hCount := GeneralPaperStoredStreamWork.rational_array_capacity model S A fieldStart
    (GeneralPaperStoredDominantCursor.rowTable row) hA hOwner
  have hCollect := GeneralPaperStoredRationalCollectionWork.work_from_owner model S A fieldStart loaded directory hChildContract
    (GeneralPaperStoredDominantCursor.rowTable row) hRead hHeader rfl hA hOwner
  obtain ⟨hValues,_,_⟩ := GeneralPaperStoredReadStreamSources.rational_array model S A fieldStart loaded directory hChildContract
    (GeneralPaperStoredDominantCursor.rowTable row) hRead hHeader rfl
  have hLength : row.data.toList.length = n := by rw [Array.length_toList,row.size]
  have hMaterialize := PaperListReferenceArray.bit_work A row.data.toList hA
    (by rw [hLength]; exact binaryWordWidth_le_of_lt_pow hA hCount)
  have hLoadWork := (GeneralPaperStoredChildRead.trace model A installed 0 0 child.root.reference hPointer).2
  have hPointerWork := GeneralPaperStoredReferenceReadWork.read_work model A A 0 0 _ installed.root child.root.reference
    (by decide) (Nat.two_pow_pos A) hPointer
  simp only [GeneralPaperStoredDominantEmission.run,hLoad,hValues]
  rw [hLoadWork]
  unfold bound
  simp only [hLength] at hMaterialize
  dsimp only [GeneralPaperStoredDominantCursor.rowTable] at *
  omega

theorem vertex_payload {n : ℕ} (budget : ℚ) (chosen : Fin n) (row : RationalResourceArray n)
    (correct : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen) :
    (row.data.toList.map rationalWordWidth).sum ≤ 3 * n + rationalWordWidth budget := by
  have hFn := GeneralPaperRowPrefix.list_ofFn (GeneralPaperStoredDominantCursor.rowTable row)
  change List.ofFn row.allocation = row.data.toList at hFn
  rw [← hFn,List.map_ofFn,List.sum_ofFn]
  have hCoordinates : row.allocation = fun j => if j = chosen then budget else 0 := by
    funext j
    exact GeneralPaperEqualBitCanonical.pure_coordinates budget chosen row correct j
  rw [hCoordinates]
  exact GeneralPaperEqualBitVertex.payload budget chosen

def vertexBound (model : RationalCostModel) (A n b : ℕ) : ℕ :=
  3 * (3 * n + b) + n * GeneralPaperStoredRationalCollectionWork.perElement model A +
    GeneralPaperStoredCountReadWork.bound model A + 192 * (A + 1) +
    64 * (n + 1) * A + GeneralPaperStoredReferenceReadWork.readBound model A A + 512 * (A + 1)

theorem vertex_bound {n : ℕ} (model : RationalCostModel) (A : ℕ) (budget : ℚ) (chosen : Fin n) (row : RationalResourceArray n)
    (correct : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen) :
    bound model A row ≤ vertexBound model A n (rationalWordWidth budget) := by
  have h := vertex_payload budget chosen row correct
  unfold bound vertexBound GeneralPaperStoredRationalCollectionWork.bound GeneralPaperStoredDominantCursor.rowTable
  dsimp only
  omega

end Blotto.GeneralPaperStoredDominantEmissionWork
