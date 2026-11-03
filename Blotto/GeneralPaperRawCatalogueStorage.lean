import Blotto.GeneralPaperActualCatalogueLookupStorage

/-! Native raw optional-entry buffers and annotations. Every prefix reserves
all occurrence slots. Lookup soundness derives entry payloads; the running
native work word also depends on the retained cell count. -/
namespace Blotto.GeneralPaperRawCatalogueStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def entryCapacity (W lambda : ℕ) : ℕ := 3*operandWidth lambda+80*W+1

theorem lookup_entry (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    GeneralPaperCodeRecordStorage.optionalEntry W (GeneralPaperLeastValidCell.run a response lo hi).selected≤entryCapacity W a.lambda := by
  apply GeneralPaperCodeRecordStorage.optional_entry W a response
  intro e he
  exact (GeneralPaperLeastValidCell.run_sound a response lo hi e he).2.2

def filledPrefix {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (cells : GeneralPaperEpochCellInstructions.Cells n) (count : ℕ) (hc : count≤n) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W n (GeneralPaperCodeRecordStorage.optionalEntry W)
    (GeneralPaperCellCatalogueExecution.fill bits index model W a response cells count hc).1.1

theorem prefix_bound {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (cells : GeneralPaperEpochCellInstructions.Cells n) (count : ℕ) (hc : count≤n) :
    filledPrefix bits index model W a response cells count hc≤n*(entryCapacity W a.lambda+W)+64*W := by
  unfold filledPrefix
  rw [GeneralPaperCellCatalogueData.fill_data]
  exact GeneralPaperEncodedReferenceVector.indexed_reserved_prefix (fun _ => 1) 1 W (entryCapacity W a.lambda)
    (GeneralPaperCodeRecordStorage.optionalEntry W) (fun r : Fin n =>
      let cell := cells.read r
      let found := GeneralPaperLeastValidCell.run a response cell.1 cell.2
      (found.selected,found.work+12)) (fun r => lookup_entry W a response (cells.read r).1 (cells.read r).2) count hc

theorem annotation_word {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (cells : GeneralPaperEpochCellInstructions.Cells n) (count : ℕ) (hc : count≤n) :
    natBits (GeneralPaperCellCatalogueExecution.fill bits index model W a response cells count hc).1.2≤
      GeneralPaperCellCatalogueOperands.width n a.lambda := by
  have h := (GeneralPaperCellCatalogueOperands.fill_annotation bits index model W a response cells count hc).trans
    (GeneralPaperCellCatalogueOperands.annotation_cap n a.lambda count hc)
  exact (Nat.add_le_add_left (binaryWordWidth_mono h) 1).trans (GeneralPaperCellCatalogueOperands.word_bound n a.lambda)

def stepFields {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (cells : GeneralPaperEpochCellInstructions.Cells n) (count : ℕ) : ℕ :=
  if h : count<n then
    let earlier := GeneralPaperCellCatalogueExecution.fill true (fun w => w) model W a response cells count h.le
    let found := GeneralPaperLeastValidCellExecution.run true model W a response
      (cells.read ⟨count,h⟩).1 (cells.read ⟨count,h⟩).2
    fields W [earlier.1.2,found.1.work,earlier.1.2+found.1.work,earlier.1.2+found.1.work+54]
  else 32*W

theorem step_bound {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (cells : GeneralPaperEpochCellInstructions.Cells n) (count : ℕ) :
    stepFields model W a response cells count≤4*(GeneralPaperCellCatalogueOperands.width n a.lambda+W)+32*W := by
  unfold stepFields
  split
  · rename_i h
    let earlier := GeneralPaperCellCatalogueExecution.fill true (fun w => w) model W a response cells count h.le
    let found := GeneralPaperLeastValidCellExecution.run true model W a response
      (cells.read ⟨count,h⟩).1 (cells.read ⟨count,h⟩).2
    have hfull := (GeneralPaperCellCatalogueOperands.fill_annotation true (fun w => w) model W a response cells (count+1) h).trans
      (GeneralPaperCellCatalogueOperands.annotation_cap n a.lambda (count+1) h)
    rw [GeneralPaperCellCatalogueExecution.fill] at hfull
    change earlier.1.2+found.1.work+54≤GeneralPaperCellCatalogueOperands.magnitude n a.lambda at hfull
    have bound (x : ℕ) (hx : x≤GeneralPaperCellCatalogueOperands.magnitude n a.lambda) :
        natBits x≤GeneralPaperCellCatalogueOperands.width n a.lambda :=
      (Nat.add_le_add_left (binaryWordWidth_mono hx) 1).trans (GeneralPaperCellCatalogueOperands.word_bound n a.lambda)
    dsimp only [earlier,found] at hfull
    apply fields_bound W (GeneralPaperCellCatalogueOperands.width n a.lambda)
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> apply bound <;> omega
  · omega

def footprint {n : ℕ} (W : ℕ) (r : FixedArrayTable n (Option GeneralPaperCodeMinimumScan.Entry) × ℕ) : ℕ :=
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperCodeRecordStorage.optionalEntry W) r.1+natBits r.2+64*W

theorem returned {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (cells : GeneralPaperEpochCellInstructions.Cells n) :
    footprint W (GeneralPaperCellCatalogueExecution.run true (fun w => w) model W a response cells).1≤
      n*(entryCapacity W a.lambda+W)+GeneralPaperCellCatalogueOperands.width n a.lambda+96*W := by
  have hv := GeneralPaperEncodedFixedVector.bounded W (entryCapacity W a.lambda) (GeneralPaperCodeRecordStorage.optionalEntry W)
    (GeneralPaperCellCatalogueExecution.run true (fun w => w) model W a response cells).1.1 (by
      intro r
      apply GeneralPaperCodeRecordStorage.optional_entry W a response
      intro e he
      exact (GeneralPaperCellCatalogueData.sound true (fun w => w) model W a response cells r e he).2)
  have hm := annotation_word true (fun w => w) model W a response cells n (Nat.le_refl _)
  change natBits (GeneralPaperCellCatalogueExecution.run true (fun w => w) model W a response cells).1.2≤_ at hm
  unfold footprint
  omega

end Blotto.GeneralPaperRawCatalogueStorage
