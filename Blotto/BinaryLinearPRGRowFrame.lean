import Blotto.BinaryLinearRowFrame
import Blotto.RationalPRGOutputHeight

/-! The linear serializer reaches both original-budget finite-bit PRG rows.
Only serialization is priced here. Row computation, array-to-list extraction,
header preparation, arithmetic and address-bit calibration remain separate. -/
namespace Blotto.BinaryLinearPRGRowFrame
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGPreparation
open BinaryLinearRowFrame
set_option autoImplicit false

theorem table_list {n : ℕ} (row : FixedArrayTable n SignedWord) :
    row.data.toList = List.ofFn row.read := by
  apply List.ext_getElem
  · simp only [Array.length_toList,List.length_ofFn,row.size]
  · intro j hj hk
    simp only [Array.getElem_toList,List.getElem_ofFn,FixedArrayTable.read]

def row (header : List Bool) {n : ℕ} (input : FixedArrayTable n SignedWord) : List Bool :=
  frame header input.data.toList

theorem row_data {n : ℕ} (input : FixedArrayTable n SignedWord) :
    row (BinaryNatFrame.encode n) input = BinaryStoredRowFrame.row input := by
  simp only [row,frame_data,table_list,BinaryStoredRowFrame.row]

def rich {n : ℕ} (header : List Bool) (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : List Bool :=
  row header (BinaryPRGOriginalSampler.richSample prepared h K bits)

def poor {n : ℕ} (header : List Bool) (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : List Bool :=
  row header (BinaryPRGOriginalSampler.poorSample prepared h K bits)

theorem rich_data {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    rich (BinaryNatFrame.encode n) prepared h K bits = BinaryStoredRowFrame.richOutput prepared h K bits :=
  row_data _

theorem poor_data {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    poor (BinaryNatFrame.encode n) prepared h K bits = BinaryStoredRowFrame.poorOutput prepared h K bits :=
  row_data _

theorem rich_read {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (suffix : List Bool) :
    BinaryRatListFrame.readRow (rich (BinaryNatFrame.encode n) prepared h K bits++suffix) =
      some (n,List.ofFn ((prepared.original.source h.2.2).richSample K bits),suffix) := by
  rw [rich_data]
  exact BinaryStoredRowFrame.richOutput_read prepared h K bits suffix

theorem poor_read {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (suffix : List Bool) :
    BinaryRatListFrame.readRow (poor (BinaryNatFrame.encode n) prepared h K bits++suffix) =
      some (n,List.ofFn ((prepared.original.source h.2.2).poorSample K bits),suffix) := by
  rw [poor_data]
  exact BinaryStoredRowFrame.poorOutput_read prepared h K bits suffix

theorem sample_widths {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (j : Fin n) :
    width ((BinaryPRGOriginalSampler.richSample prepared h K bits).read j) ≤
        2^77*((prepared.original.source h.2.2).originalInputWordWidth+K+6) ∧
      width ((BinaryPRGOriginalSampler.poorSample prepared h K bits).read j) ≤
        2^77*((prepared.original.source h.2.2).originalInputWordWidth+K+6) := by
  have hr := BinaryPRGOriginalSampler.richSample_refines prepared h K bits
  have hp := BinaryPRGOriginalSampler.poorSample_refines prepared h K bits
  change (fun j => value ((BinaryPRGOriginalSampler.richSample prepared h K bits).read j)) = _ at hr
  change (fun j => value ((BinaryPRGOriginalSampler.poorSample prepared h K bits).read j)) = _ at hp
  have hs := (prepared.original.source h.2.2).sample_wordWidths_linear K bits j
  constructor
  · exact (BinaryPRGOriginalSampler.richSample_canonical prepared h K bits j).2.trans
      (by rw [congrFun hr j]; exact hs.1)
  · exact (BinaryPRGOriginalSampler.poorSample_canonical prepared h K bits j).2.trans
      (by rw [congrFun hp j]; exact hs.2)

theorem serialization_bound {n : ℕ} (header : List Bool) (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    let W := 2^77*((prepared.original.source h.2.2).originalInputWordWidth+K+6)
    (frameRun header (BinaryPRGOriginalSampler.richSample prepared h K bits).data.toList).trace.length ≤
        3*header.length+17*n*(W+1)+4 ∧
      (frameRun header (BinaryPRGOriginalSampler.poorSample prepared h K bits).data.toList).trace.length ≤
        3*header.length+17*n*(W+1)+4 := by
  dsimp only
  have hr := (frame_linear header (List.ofFn (BinaryPRGOriginalSampler.richSample prepared h K bits).read)
    _ (by intro word hw; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw; exact (sample_widths prepared h K bits j).1)).1
  have hp := (frame_linear header (List.ofFn (BinaryPRGOriginalSampler.poorSample prepared h K bits).read)
    _ (by intro word hw; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw; exact (sample_widths prepared h K bits j).2)).1
  simpa only [table_list,List.length_ofFn] using And.intro hr hp

theorem serialization_allocation_prefix {n : ℕ} (header : List Bool) (prepared : Prepared n) (h : prepared.Valid)
    (K used : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    cells ((frameRun header (BinaryPRGOriginalSampler.richSample prepared h K bits).data.toList).trace.take used) ≤
        (rich header prepared h K bits).length ∧
      cells ((frameRun header (BinaryPRGOriginalSampler.poorSample prepared h K bits).data.toList).trace.take used) ≤
        (poor header prepared h K bits).length := by
  constructor
  · exact (allocation_prefix _ _ used).trans_eq (frame_cells_exact _ _)
  · exact (allocation_prefix _ _ used).trans_eq (frame_cells_exact _ _)

theorem output_budgets {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    BinaryRatListFrame.FullBudgetList (value prepared.original.a)
      (List.ofFn ((prepared.original.source h.2.2).richSample K bits)) ∧
      BinaryRatListFrame.FullBudgetList (value prepared.original.b)
        (List.ofFn ((prepared.original.source h.2.2).poorSample K bits)) :=
  BinaryStoredRowFrame.output_budgets prepared h K bits

end Blotto.BinaryLinearPRGRowFrame
