import Blotto.GeneralPaperStoredNaturalCollectionWork
import Blotto.GeneralPaperStoredRecordReadWork
import Blotto.GeneralPaperStoredPreparedRead

/-! Prepared controls are collected once from their counted stored list.
The original budget read is payload sensitive. Scalar ownership also derives
the midpoint-buffer capacity from the retained denominator's encoding. -/
namespace Blotto.GeneralPaperStoredPreparedReadWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperRetainedScalarValue (Scalar)
open GeneralPaperStoredReadContext (Context)
open GeneralPaperUnifiedFieldValue (referenceMemory)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def controlsBound (model : RationalCostModel) (A : ℕ) (prepared : GeneralPaperEqualPreparedCache.Prepared G l) : ℕ :=
  GeneralPaperStoredNaturalCollectionWork.bound model A (GeneralPaperPreparedRecordCursor.controls prepared) +
    GeneralPaperStoredReferenceReadWork.readBound model A A + 256 * (A + 1)

def controlsMajorant (model : RationalCostModel) (A P : ℕ) : ℕ :=
  12 * P + 4 * GeneralPaperStoredNaturalCollectionWork.perElement model A +
    GeneralPaperStoredCountReadWork.bound model A + GeneralPaperStoredReferenceReadWork.readBound model A A + 448 * (A + 1)

theorem controls_bound (model : RationalCostModel) (A P : ℕ) (prepared : GeneralPaperEqualPreparedCache.Prepared G l)
    (hControl : ∀ x ∈ GeneralPaperPreparedRecordCursor.controls prepared,GeneralPaperEncodedScalarStorage.natBits x ≤ P) :
    controlsBound model A prepared ≤ controlsMajorant model A P := by
  have hD := hControl prepared.D (by simp [GeneralPaperPreparedRecordCursor.controls])
  have hRange := hControl prepared.rangeBits (by simp [GeneralPaperPreparedRecordCursor.controls])
  have hBits := hControl prepared.midpointBits (by simp [GeneralPaperPreparedRecordCursor.controls])
  have hCount := hControl prepared.midpointCount (by simp [GeneralPaperPreparedRecordCursor.controls])
  simp only [controlsBound,controlsMajorant,GeneralPaperStoredNaturalCollectionWork.bound,
    GeneralPaperPreparedRecordCursor.controls,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil]
  omega

theorem controls_work (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (prepared : GeneralPaperEqualPreparedCache.Prepared G l)
    (hRead : Readback model A installed (GeneralPaperPreparedRecordCursor.expected model S A prepared start))
    (hHeaders : ∀ header ∈ (GeneralPaperPreparedRecordCursor.expected model S A prepared start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperPreparedRecordCursor.expected model S A prepared start).root.reference) :
    (GeneralPaperStoredPreparedRead.controls model A installed).work ≤ controlsBound model A prepared := by
  obtain ⟨fieldStart,hLoad,_,hChildRead,hChildHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperPreparedRecordCursor.schema model S A prepared) (GeneralPaperPreparedRecordCursor.child model S A prepared)
    GeneralPaperPreparedRecordCursor.fields hRead hRoot ⟨3,by decide⟩
  let child := GeneralPaperPreparedRecordCursor.child model S A prepared .controls fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hHeader : GeneralPaperRetainedHeaderCountSources.listHeader model S A fieldStart 32 1
      ((GeneralPaperPreparedRecordCursor.controls prepared).map Scalar.natural) ∈ full.headers :=
    hHeaders _ (hChildHeaders _ (List.mem_singleton_self _))
  have hValues := GeneralPaperStoredNaturalCollectionWork.work model S A layoutStart fieldStart plan full loaded
    (GeneralPaperStoredReadContext.atRoot ctx child.root.reference) (GeneralPaperPreparedRecordCursor.controls prepared)
    hChildRead hHeader rfl
  have hLoadWork := GeneralPaperStoredRecordReadWork.work model S A layoutStart start 64 plan full installed ctx
    (GeneralPaperPreparedRecordCursor.schema model S A prepared) (GeneralPaperPreparedRecordCursor.child model S A prepared)
    GeneralPaperPreparedRecordCursor.fields hRead hHeaders hRoot ⟨3,by decide⟩
  change (GeneralPaperStoredChildRead.load model A installed 0 3).1 = some (⟨A,loaded⟩ : GeneralPaperStoredChildRead.Child) at hLoad
  change (GeneralPaperStoredChildRead.load model A installed 0 3).2 ≤ _ at hLoadWork
  change (GeneralPaperStoredRecordCollectors.naturals model A installed 3).work ≤ _
  rw [(GeneralPaperStoredRecordCollectors.naturals_trace model A installed loaded 3 hLoad).2.2]
  unfold controlsBound
  omega

theorem budget_work (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (prepared : GeneralPaperEqualPreparedCache.Prepared G l)
    (hRead : Readback model A installed (GeneralPaperPreparedRecordCursor.expected model S A prepared start))
    (hHeaders : ∀ header ∈ (GeneralPaperPreparedRecordCursor.expected model S A prepared start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperPreparedRecordCursor.expected model S A prepared start).root.reference) :
    (GeneralPaperStoredPreparedRead.budget model A installed).2 ≤
      2 * rationalWordWidth prepared.budget + GeneralPaperStoredScalarReadWork.overhead model A := by
  obtain ⟨fieldStart,_,hPointer,hChildRead,_,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperPreparedRecordCursor.schema model S A prepared) (GeneralPaperPreparedRecordCursor.child model S A prepared)
    GeneralPaperPreparedRecordCursor.fields hRead hRoot ⟨4,by decide⟩
  let child := GeneralPaperPreparedRecordCursor.child model S A prepared .budget fieldStart
  let cell : GeneralPaperScalarFieldCursor.Cell A := ⟨child.root,.rational prepared.budget⟩
  have hScalar := (hChildRead.2 cell (List.mem_singleton_self _)).1
  have h := GeneralPaperStoredScalarRead.trace model A installed 0 4 child.root.reference (.rational prepared.budget) hPointer hScalar
  have hCount := GeneralPaperStoredReadContext.header_count_fits ctx _ (hHeaders _
    (GeneralPaperStoredRecordReadWork.member A start 64 (GeneralPaperPreparedRecordCursor.schema model S A prepared)
      (GeneralPaperPreparedRecordCursor.child model S A prepared) GeneralPaperPreparedRecordCursor.fields))
  rw [GeneralPaperStoredRecordReadWork.count] at hCount
  have hPointerWork := GeneralPaperStoredReferenceReadWork.read_work model A A 0 4 _ installed.root child.root.reference
    (by decide) (by change 5 < 2 ^ A at hCount; omega) hPointer
  rw [(GeneralPaperStoredPreparedRead.budget_source model S A start installed prepared hRead hRoot).2,h.2]
  simp only [GeneralPaperRetainedScalarValue.encode] at *
  unfold GeneralPaperStoredScalarReadWork.overhead
  omega

theorem cell_size {model : RationalCostModel} {S A layoutStart : ℕ} {plan : GeneralPaperMeasuredBlockPlan.Plan}
    {full : Directory A} {installed : Installed A} (ctx : Context model S A layoutStart plan full installed)
    (cell : GeneralPaperScalarFieldCursor.Cell A) (hCell : cell ∈ full.cells) :
    GeneralPaperRetainedScalarValue.encode cell.value < 2 ^ A := by
  have hRegion := ctx.safe.2.2.1.subset (List.mem_map.mpr ⟨cell,hCell,rfl⟩)
  have hRange := GeneralPaperSequentialLayout.range model S A layoutStart plan.sizes cell.region hRegion
  have hFits := ctx.safe.2.2.2.2 cell hCell
  change cell.region.length = GeneralPaperRetainedScalarValue.encode cell.value at hFits
  have hStop := hRange.2.trans_lt ctx.capacity
  change cell.region.start + cell.region.length < _ at hStop
  omega

theorem midpoint_capacity (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (prepared : GeneralPaperEqualPreparedCache.Prepared G l)
    (hRead : Readback model A installed (GeneralPaperPreparedRecordCursor.expected model S A prepared start))
    (hCells : ∀ cell ∈ (GeneralPaperPreparedRecordCursor.expected model S A prepared start).cells,cell ∈ full.cells)
    (hRoot : installed.root = (GeneralPaperPreparedRecordCursor.expected model S A prepared start).root.reference) :
    prepared.midpointBits + 2 < 2 ^ A := by
  obtain ⟨fieldStart,_,_,_,_,hChildCells⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperPreparedRecordCursor.schema model S A prepared) (GeneralPaperPreparedRecordCursor.child model S A prepared)
    GeneralPaperPreparedRecordCursor.fields hRead hRoot ⟨3,by decide⟩
  let values := (GeneralPaperPreparedRecordCursor.controls prepared).map Scalar.natural
  let regions := (GeneralPaperSequentialLayout.run model S A (fieldStart + A * (1 * values.length + 32))
    (values.map GeneralPaperRetainedScalarValue.encode)).1
  have hLength : regions.length = values.length := by
    dsimp only [regions]
    rw [GeneralPaperSequentialLayout.count,List.length_map]
  have hValues := GeneralPaperScalarFieldCursor.cells_values A regions values hLength
  obtain ⟨cell,hCell,_,hValue⟩ := GeneralPaperRecordScalarRead.cell_lookup A _ values hValues ⟨3,by change 3 < 4; decide⟩
  have hFull : cell ∈ full.cells := hCells cell (hChildCells cell hCell)
  have hSize := cell_size ctx cell hFull
  change cell.value = .natural prepared.midpointCount at hValue
  rw [hValue] at hSize
  simp only [GeneralPaperRetainedScalarValue.encode,GeneralPaperEncodedScalarStorage.natBits,
    prepared.midpointCount_correct,binaryWordWidth,Nat.log2_two_pow] at hSize
  omega

end Blotto.GeneralPaperStoredPreparedReadWork
