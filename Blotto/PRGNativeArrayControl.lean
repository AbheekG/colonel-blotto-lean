import Blotto.NativeArrayConversionControl
import Blotto.BinaryPRGSeedCountLifetime

/-! Original raw-frame length instantiates source array-control widths at
actual PRG value/normalized-array and seed-array interfaces. Payload words are
not treated as small scalars. These source-control certificates do not assert
host USize/capacity behavior or complete reference-bit/time/space prices. -/
namespace Blotto.PRGNativeArrayControl
open NativeArrayConversionCore
open RationalLottoResourceSystem

abbrev Parsed := (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool

theorem dimension_bound (frame : List Bool) (parsed : Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) : parsed.1.1 ≤ frame.length :=
  BinaryPRGSeedRequestBound.read_dimension_bound frame parsed
    ((BinaryPRGRawRequestLifetime.readWithTrace_state frame).symm.trans hRead)

theorem game_frame_pack_control (frame : List Bool)
    (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (hRead : (BinaryPRGGameFrameLifetime.readWithTrace frame).1 = some parsed) :
    parsed.1.2.game.input.values.data = (pack parsed.1.2.rows).1 ∧
    ((pack parsed.1.2.rows).2.filterMap NativeArrayConversionControl.PushSnapshot.pushIndex) = List.range parsed.1.1 ∧
    (pack parsed.1.2.rows).2.length = parsed.1.1+1 ∧
    ∀ s ∈ (pack parsed.1.2.rows).2,
      ∀ value ∈ s.operands parsed.1.1,
        binaryWordWidth value ≤ binaryWordWidth (frame.length+1) := by
  have hDimension : parsed.1.1 ≤ frame.length :=
    (BinaryDecodedInputLength.parsed_sizes frame parsed
      ((BinaryPRGNormalizedFrameWork.read_state frame).trans
        ((BinaryPRGGameFrameLifetime.readWithTrace_original frame).symm.trans hRead))).1
  have hRows := parsed.1.2.rows_length
  refine ⟨?_,?_,?_,?_⟩
  · rw [pack_state]
    apply Array.toList_inj.mp
    rw [List.toList_toArray]
    rw [parsed.1.2.rows_readback]
    apply List.ext_getElem
    · simp [List.length_ofFn,parsed.1.2.game.input.values.size]
    · intro i hi hj
      simp [FixedArrayTable.read]
  · simp only [NativeArrayConversionControl.pack_indices,hRows]
  · simp only [pack_length,hRows]
  · intro s hs value hv
    have h := NativeArrayConversionControl.pack_scalar_width parsed.1.2.rows s hs value
      (by simpa only [hRows] using hv)
    rw [hRows] at h
    exact h.trans (binaryWordWidth_mono (Nat.add_le_add_right hDimension 1))

theorem game_frame_pack_source_usage (frame : List Bool)
    (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (hRead : (BinaryPRGGameFrameLifetime.readWithTrace frame).1 = some parsed) :
    parsed.1.2.game.input.values.data = (BinaryLifetimeListArray.tableWithTrace parsed.1.2.rows).1.data ∧
    BinaryPRGHeapTraceUsage.usage (BinaryLifetimeListArray.tableWithTrace parsed.1.2.rows).2 ≤
      frame.length*(frame.length+1)+frame.length+1 := by
  have hControl := game_frame_pack_control frame parsed hRead
  have hDimension : parsed.1.1 ≤ frame.length :=
    (BinaryDecodedInputLength.parsed_sizes frame parsed
      ((BinaryPRGNormalizedFrameWork.read_state frame).trans
        ((BinaryPRGGameFrameLifetime.readWithTrace_original frame).symm.trans hRead))).1
  have hRows : parsed.1.2.rows.length ≤ frame.length := parsed.1.2.rows_length.le.trans hDimension
  refine ⟨?_,?_⟩
  · rw [hControl.1,NativeArrayConversionControl.pack_source]
    rfl
  · exact (BinaryLifetimeListArray.tableWithTrace_usage parsed.1.2.rows).trans (by gcongr)

theorem game_frame_pack_prefixSlots (frame : List Bool)
    (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (hRead : (BinaryPRGGameFrameLifetime.readWithTrace frame).1 = some parsed) :
    NativeArrayConversionControl.prefixSlots (pack parsed.1.2.rows).2 ≤ (frame.length+1)^2 := by
  have hDimension : parsed.1.1 ≤ frame.length :=
    (BinaryDecodedInputLength.parsed_sizes frame parsed
      ((BinaryPRGNormalizedFrameWork.read_state frame).trans
        ((BinaryPRGGameFrameLifetime.readWithTrace_original frame).symm.trans hRead))).1
  have hRows : parsed.1.2.rows.length ≤ frame.length := parsed.1.2.rows_length.le.trans hDimension
  exact (NativeArrayConversionControl.pack_prefixSlots parsed.1.2.rows).trans (by gcongr)

theorem count_bound (frame : List Bool) (parsed : Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    sampleBitBudget parsed.1.1 parsed.1.2.request.precision ≤ BinaryPRGSeedRequestBound.seedCountBound frame.length :=
  BinaryPRGSeedRequestBound.read_seedCount_bound frame parsed
    ((BinaryPRGRawRequestLifetime.readWithTrace_state frame).symm.trans hRead)

theorem raw_build_scalar_width {α : Type*} (frame : List Bool) (parsed : Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) (produce : Fin parsed.1.1 → α) :
    ∀ s ∈ (NativeArrayCoreControl.build produce).2,∀ value ∈ s.operands parsed.1.1,
      binaryWordWidth value ≤ binaryWordWidth (frame.length+1) := by
  intro s hs value hv
  exact (NativeArrayBuildControl.build_scalar_width produce s hs value hv).trans
    (binaryWordWidth_mono (Nat.add_le_add_right (dimension_bound frame parsed hRead) 1))

theorem raw_values_read_scalar_width (frame : List Bool) (parsed : Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    ∀ s ∈ (read parsed.1.2.request.prepared.original.values.data).2,
      ∀ value ∈ s.operands parsed.1.2.request.prepared.original.values.data.size,
        binaryWordWidth value ≤ binaryWordWidth (frame.length+1) := by
  intro s hs value hv
  have h := NativeArrayConversionControl.read_scalar_width parsed.1.2.request.prepared.original.values.data s hs value hv
  rw [parsed.1.2.request.prepared.original.values.size] at h
  exact h.trans (binaryWordWidth_mono (Nat.add_le_add_right (dimension_bound frame parsed hRead) 1))

theorem raw_row_pack_scalar_width {α : Type*} (frame : List Bool) (parsed : Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rows : List α) (hLength : rows.length = parsed.1.1) :
    ∀ s ∈ (pack rows).2,∀ value ∈ s.operands rows.length,binaryWordWidth value ≤ binaryWordWidth (frame.length+1) := by
  intro s hs value hv
  have h := NativeArrayConversionControl.pack_scalar_width rows s hs value hv
  rw [hLength] at h
  exact h.trans (binaryWordWidth_mono (Nat.add_le_add_right (dimension_bound frame parsed hRead) 1))

theorem raw_values_index_words {α : Type*} (frame : List Bool) (parsed : Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) (produce : Fin parsed.1.1 → α) :
    ((BooleanArrayIndexEnumeration.enumerateWithTrace parsed.1.2.request.prepared.original.values.data.toList).1.map
      BinaryCarryCounter.value) = (NativeArrayCoreControl.build produce).2.filterMap NativeArrayCoreControl.Snapshot.callback ∧
    ∀ word ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace parsed.1.2.request.prepared.original.values.data.toList).1,
      word.length ≤ binaryWordWidth frame.length := by
  have hSize : parsed.1.2.request.prepared.original.values.data.toList.length = parsed.1.1 := by
    rw [Array.length_toList,parsed.1.2.request.prepared.original.values.size]
  refine ⟨BooleanArrayIndexEnumeration.native_builder_indices _ hSize produce,?_⟩
  intro word hWord
  have h := BooleanArrayIndexEnumeration.enumerate_width parsed.1.2.request.prepared.original.values.data.toList word hWord
  rw [hSize] at h
  exact h.trans (binaryWordWidth_mono (dimension_bound frame parsed hRead))

def seedArrays {n K : ℕ} (tables : BinaryPRGSeedBlocks.Tables n K) : List (Array Bool) :=
  [tables.choice.data,tables.scalar.data,tables.outer.data]

theorem seed_array_size {n K : ℕ} (tables : BinaryPRGSeedBlocks.Tables n K) :
    ∀ data ∈ seedArrays tables,data.size ≤ sampleBitBudget n K := by
  intro data hData
  simp only [seedArrays,List.mem_cons,List.not_mem_nil,or_false] at hData
  rcases hData with rfl|rfl|rfl
  · rw [tables.choice.size,sampleBitBudget_eq]
    unfold coinBitBudget
    omega
  · rw [tables.scalar.size,sampleBitBudget_eq]
    omega
  · rw [tables.outer.size,sampleBitBudget_eq]
    omega

theorem raw_seed_read_scalar_width (frame : List Bool) (parsed : Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (tables : BinaryPRGSeedBlocks.Tables parsed.1.1 parsed.1.2.request.precision) :
    ∀ data ∈ seedArrays tables,∀ s ∈ (read data).2,∀ value ∈ s.operands data.size,
      binaryWordWidth value ≤ binaryWordWidth (BinaryPRGSeedRequestBound.seedCountBound frame.length+1) := by
  intro data hData s hs value hv
  have hSize := (seed_array_size tables data hData).trans (count_bound frame parsed hRead)
  exact (NativeArrayConversionControl.read_scalar_width data s hs value hv).trans
    (binaryWordWidth_mono (Nat.add_le_add_right hSize 1))

theorem raw_seed_pack_scalar_width (frame : List Bool) (parsed : Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (choice scalar outer : List Bool)
    (hChoice : choice.length = coinBitBudget parsed.1.1 parsed.1.2.request.precision)
    (hScalar : scalar.length = parsed.1.2.request.precision) (hOuter : outer.length = parsed.1.2.request.precision) :
    ∀ items ∈ [choice,scalar,outer],∀ s ∈ (pack items).2,∀ value ∈ s.operands items.length,
      binaryWordWidth value ≤ binaryWordWidth (BinaryPRGSeedRequestBound.seedCountBound frame.length+1) := by
  have hBound := count_bound frame parsed hRead
  have hSmall : coinBitBudget parsed.1.1 parsed.1.2.request.precision ≤
      sampleBitBudget parsed.1.1 parsed.1.2.request.precision ∧
      parsed.1.2.request.precision ≤ sampleBitBudget parsed.1.1 parsed.1.2.request.precision := by
    unfold sampleBitBudget innerBitBudget
    omega
  intro items hItems s hs value hv
  have hLength : items.length ≤ BinaryPRGSeedRequestBound.seedCountBound frame.length := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hItems
    rcases hItems with rfl|rfl|rfl <;> omega
  exact (NativeArrayConversionControl.pack_scalar_width items s hs value hv).trans
    (binaryWordWidth_mono (Nat.add_le_add_right hLength 1))

theorem raw_seed_reads_once (frame : List Bool) (parsed : Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (tables : BinaryPRGSeedBlocks.Tables parsed.1.1 parsed.1.2.request.precision) :
    ∀ data ∈ seedArrays tables,((read data).2.filterMap ReadSnapshot.readIndex).length = data.size ∧
      data.size ≤ BinaryPRGSeedRequestBound.seedCountBound frame.length := by
  intro data hData
  exact ⟨NativeArrayConversionControl.read_count data,(seed_array_size tables data hData).trans (count_bound frame parsed hRead)⟩

theorem raw_seed_index_words (frame : List Bool) (parsed : Parsed)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (tables : BinaryPRGSeedBlocks.Tables parsed.1.1 parsed.1.2.request.precision) :
    ∀ data ∈ seedArrays tables,
      ((BooleanArrayIndexEnumeration.enumerateWithTrace data.toList).1.reverse.map BinaryCarryCounter.value) =
        (read data).2.filterMap ReadSnapshot.readIndex ∧
      ∀ word ∈ (BooleanArrayIndexEnumeration.enumerateWithTrace data.toList).1,
        word.length ≤ binaryWordWidth (BinaryPRGSeedRequestBound.seedCountBound frame.length) := by
  intro data hData
  refine ⟨NativeArrayConversionControl.read_indices_boolean data data.toList (Array.length_toList),?_⟩
  intro word hWord
  have h := BooleanArrayIndexEnumeration.enumerate_width data.toList word hWord
  rw [Array.length_toList] at h
  exact h.trans (binaryWordWidth_mono ((seed_array_size tables data hData).trans (count_bound frame parsed hRead)))

end Blotto.PRGNativeArrayControl
