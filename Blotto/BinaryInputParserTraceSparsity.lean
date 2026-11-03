import Blotto.BinaryArithmeticTraceSparsity
import Blotto.BinaryPRGGameFrameLifetime
import Blotto.BinaryAccuracyLifetime
import Blotto.BinaryPRGRequestRulers

/-! Actual input framing and accuracy traces satisfy the structural event
certificate on every input, including rejected and truncated frames. -/
namespace Blotto.BinaryInputParserTraceSparsity
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization BinaryRationalEncoding
open BinaryMeasuredTraceSparsity
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem find_bound (bits : List Bool) : Bounded (BinaryUnaryPayloadLifetime.findWithTrace bits).2 := by
  induction bits with
  | nil => exact wrap_bound 8 1 [] (by simp) (by decide)
  | cons bit rest ih =>
      cases bit
      · apply wrap_bound 8 1 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
        simpa only [List.forall_mem_cons,children_nil,and_true] using ih
      · exact wrap_bound 8 1 [] (by simp) (by decide)

theorem consume_reversed_bound (ruler payload reversed : List Bool) :
    Bounded (BinaryUnaryPayloadLifetime.consumeReversedWithTrace ruler payload reversed).2 := by
  induction ruler generalizing payload reversed with
  | nil => exact wrap_bound 8 1 [] (by simp) (by decide)
  | cons bit rest ih =>
      cases bit
      · cases payload with
        | nil => exact wrap_bound 8 1 [] (by simp) (by decide)
        | cons next tail =>
            apply wrapList_bound 1 8 1 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
            simpa only [List.forall_mem_cons,children_nil,and_true] using ih tail (next::reversed)
      · exact wrap_bound 8 1 [] (by simp) (by decide)

theorem unary_reversed_bound (bits : List Bool) : Bounded (BinaryUnaryPayloadLifetime.readReversedWithTrace bits).2 := by
  unfold BinaryUnaryPayloadLifetime.readReversedWithTrace
  dsimp only
  split
  · apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using find_bound bits
  · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨find_bound _,consume_reversed_bound _ _ _⟩

theorem unary_bound (bits : List Bool) : Bounded (BinaryUnaryPayloadLifetime.readWithTrace bits).2 := by
  unfold BinaryUnaryPayloadLifetime.readWithTrace
  dsimp only
  split
  · apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using unary_reversed_bound bits
  · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨unary_reversed_bound _,of_sparse _ (BinaryInitialTraceSparsity.reverse_sparse _ _)⟩

theorem drop_bound (bits : List Bool) : Bounded (BinaryStoredDimensionHeaderLifetime.dropWithTrace bits).2 := by
  induction bits with
  | nil => exact wrap_bound 8 1 [] (by simp) (by decide)
  | cons bit rest ih =>
      cases bit
      · apply wrap_bound 8 1 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
        simpa only [List.forall_mem_cons,children_nil,and_true] using ih
      · exact wrapList_bound 1 8 1 [] (by simp) (by decide)

theorem dimension_trim_bound (bits : List Bool) : Bounded (BinaryStoredDimensionHeaderLifetime.trimWithTrace bits).2 := by
  apply wrap_bound 32 (2*bits.length+4) _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨of_sparse _ (BinaryInitialTraceSparsity.reverse_sparse _ _),drop_bound _,
    of_sparse _ (BinaryInitialTraceSparsity.reverse_sparse _ _)⟩

theorem dimension_prepare_bound (bits : List Bool) : Bounded (BinaryStoredDimensionHeaderLifetime.prepareWithTrace bits).2 := by
  apply wrapList_bound _ 32 _ _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simpa only [List.forall_mem_cons,children_nil,and_true] using dimension_trim_bound bits

theorem dimension_bound (bits : List Bool) : Bounded (BinaryStoredDimensionHeaderLifetime.readWithTrace bits).2 := by
  unfold BinaryStoredDimensionHeaderLifetime.readWithTrace
  dsimp only
  split
  · apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using unary_bound bits
  · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨unary_bound _,dimension_prepare_bound _⟩

theorem canonical_bound (bits : List Bool) : Bounded (BinaryCanonicalFrameLifetime.readWithTrace bits).2 := by
  unfold BinaryCanonicalFrameLifetime.readWithTrace
  split
  · exact wrap_bound 8 1 [] (by simp) (by decide)
  · dsimp only
    split
    · apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simpa only [List.forall_mem_cons,children_nil,and_true] using unary_bound _
    · split
      · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
        simp only [List.forall_mem_cons,children_nil,and_true]
        exact ⟨unary_bound _,unary_bound _⟩
      · split
        · apply wrap_bound 64 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
          simp only [List.forall_mem_cons,children_nil,and_true]
          exact ⟨unary_bound _,unary_bound _,of_sparse _ (BinaryInitialTraceSparsity.scan_sparse _),
            BinaryArithmeticTraceSparsity.canonicalize_bound _⟩
        · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
          simp only [List.forall_mem_cons,children_nil,and_true]
          exact ⟨unary_bound _,unary_bound _,of_sparse _ (BinaryInitialTraceSparsity.scan_sparse _)⟩

theorem predecessor_bound (bits : List Bool) : Bounded (BinaryStoredCountdownLifetime.predecessorWithTrace bits).2 := by
  induction bits with
  | nil => exact wrap_bound 8 1 [] (by simp) (by decide)
  | cons bit rest ih =>
      cases bit
      · apply wrapList_bound 1 8 1 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
        simpa only [List.forall_mem_cons,children_nil,and_true] using ih
      · exact wrapList_bound 1 8 1 [] (by simp) (by decide)

theorem dimension_row_bound (counter bits : List Bool) :
    Bounded (BinaryStoredDimensionRowLifetime.readWithTrace counter bits).2 := by
  unfold BinaryStoredDimensionRowLifetime.readWithTrace
  dsimp only
  split
  · split
    · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simp only [List.forall_mem_cons,children_nil,and_true]
      exact ⟨of_sparse _ (BinaryInitialTraceSparsity.scan_sparse _),canonical_bound _⟩
    · apply wrapList_bound 1 48 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simp only [List.forall_mem_cons,children_nil,and_true]
      exact ⟨of_sparse _ (BinaryInitialTraceSparsity.scan_sparse _),canonical_bound _,predecessor_bound _,dimension_row_bound _ _⟩
  · apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using of_sparse _ (BinaryInitialTraceSparsity.scan_sparse counter)
termination_by bits.length
decreasing_by
  apply BinaryCanonicalFrameLifetime.read_suffix_lt
  assumption

theorem game_pack_bound {n : ℕ} (header : BinaryPRGHeaderFrame.Header n)
    (first second : {word : SignedWord // CanonicalWord word})
    (rest : BinaryPRGFrame.Words n × List Bool) :
    Bounded (BinaryPRGGameFrameLifetime.packWithTrace header first second rest).2 := by
  apply wrap_bound 32 (rest.1.row.length+2) _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simpa only [List.forall_mem_cons,children_nil,and_true,BinaryLifetimeListArray.tableWithTrace] using toArray_bound rest.1.row

theorem game_bound (bits : List Bool) : Bounded (BinaryPRGGameFrameLifetime.readWithTrace bits).2 := by
  unfold BinaryPRGGameFrameLifetime.readWithTrace
  dsimp only
  split
  · apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using dimension_bound bits
  · split
    · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simp only [List.forall_mem_cons,children_nil,and_true]
      exact ⟨dimension_bound _,canonical_bound _⟩
    · split
      · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
        simp only [List.forall_mem_cons,children_nil,and_true]
        exact ⟨dimension_bound _,canonical_bound _,canonical_bound _⟩
      · split
        · apply wrap_bound 40 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
          simp only [List.forall_mem_cons,children_nil,and_true]
          exact ⟨dimension_bound _,canonical_bound _,canonical_bound _,dimension_row_bound _ _⟩
        · apply wrap_bound 80 _ _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
          simp only [List.forall_mem_cons,children_nil,and_true]
          exact ⟨dimension_bound _,canonical_bound _,canonical_bound _,dimension_row_bound _ _,game_pack_bound _ _ _ _⟩

theorem positive_parse_bound (bits : List Bool) : Bounded (BinaryPositiveWordLifetime.parseWithTrace bits).2 := by
  apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simpa only [List.forall_mem_cons,children_nil,and_true] using drop_bound bits

theorem positive_bound (bits : List Bool) : Bounded (BinaryPositiveWordLifetime.readWithTrace bits).2 := by
  unfold BinaryPositiveWordLifetime.readWithTrace
  dsimp only
  split
  · apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using unary_reversed_bound bits
  · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨unary_reversed_bound _,positive_parse_bound _⟩

theorem difference_bound (a b : List Bool) : Bounded (BinaryRulerControlLifetime.differenceWithTrace a b).2 := by
  induction a generalizing b with
  | nil => cases b <;> exact wrap_bound 8 1 [] (by simp) (by decide)
  | cons bit rest ih => cases b with
    | nil => exact wrap_bound 8 1 [] (by simp) (by decide)
    | cons other tail =>
        apply wrap_bound 8 1 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
        simpa only [List.forall_mem_cons,children_nil,and_true] using ih tail

theorem compare_length_bound (a b : List Bool) : Bounded (BinaryRulerControlLifetime.compareLengthWithTrace a b).2 := by
  induction a generalizing b with
  | nil => cases b <;> exact wrap_bound 8 1 [] (by simp) (by decide)
  | cons bit rest ih => cases b with
    | nil => exact wrap_bound 8 1 [] (by simp) (by decide)
    | cons other tail =>
        apply wrap_bound 8 1 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
        simpa only [List.forall_mem_cons,children_nil,and_true] using ih tail

theorem le_scan_bound (a b : List Bool) : Bounded (BinaryRulerControlLifetime.leScanWithTrace a b).2 := by
  induction a generalizing b with
  | nil => exact wrap_bound 8 1 [] (by simp) (by decide)
  | cons bit rest ih => cases b with
    | nil => exact wrap_bound 8 1 [] (by simp) (by decide)
    | cons other tail =>
        unfold BinaryRulerControlLifetime.leScanWithTrace
        split
        · apply wrap_bound 8 1 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
          simpa only [List.forall_mem_cons,children_nil,and_true] using ih tail
        · exact wrap_bound 8 1 [] (by simp) (by decide)

theorem false_map_bound (bits : List Bool) : Bounded (BinaryRulerControlLifetime.falseMapWithTrace bits).2 := by
  induction bits with
  | nil => exact wrap_bound 8 1 [] (by simp) (by decide)
  | cons bit rest ih =>
      apply wrapList_bound 1 8 1 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simpa only [List.forall_mem_cons,children_nil,and_true] using ih

theorem shifted_bound (word : PositiveBinaryWord) (ruler : List Bool) : Bounded (BinaryRulerPrecisionLifetime.shiftedWithTrace word ruler).2 := by
  apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨false_map_bound _,of_sparse _ (BinaryArithmeticTraceSparsity.append_sparse _ _)⟩

theorem le_bound (a b : PositiveBinaryWord) : Bounded (BinaryRulerPrecisionLifetime.leWithTrace a b).2 := by
  unfold BinaryRulerPrecisionLifetime.leWithTrace
  dsimp only
  split
  · apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using compare_length_bound _ _
  · apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using compare_length_bound _ _
  · apply wrapList_bound 2 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨compare_length_bound _ _,le_scan_bound _ _⟩

theorem ruler_prepare_bound (a b : PositiveBinaryWord) : Bounded (BinaryRulerPrecisionLifetime.prepareWithTrace a b).2 := by
  apply wrapList_bound 1 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨difference_bound _ _,shifted_bound _ _,le_bound _ _⟩

theorem precision_bound (a b : PositiveBinaryWord) : Bounded (BinaryRulerPrecisionLifetime.precisionWithTrace a b).2 := by
  apply wrap_bound 16 _ _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simpa only [List.forall_mem_cons,children_nil,and_true] using ruler_prepare_bound a b

theorem accuracy_prepare_bound (words : BinaryAccuracyWords) : Bounded (BinaryAccuracyLifetime.prepareWithTrace words).2 := by
  apply wrapList_bound 5 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨shifted_bound _ _,precision_bound _ _⟩

theorem accuracy_bound (bits : List Bool) : Bounded (BinaryAccuracyLifetime.readWithTrace bits).2 := by
  unfold BinaryAccuracyLifetime.readWithTrace
  dsimp only
  split
  · apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using positive_bound bits
  · split
    · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simp only [List.forall_mem_cons,children_nil,and_true]
      exact ⟨positive_bound _,positive_bound _⟩
    · apply wrap_bound 48 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simp only [List.forall_mem_cons,children_nil,and_true]
      exact ⟨positive_bound _,positive_bound _,accuracy_prepare_bound _⟩

theorem triple_bound {α : Type*} (rows : List α) (tail : List Bool) : Bounded (BinaryPRGRequestRulers.tripleWithTrace rows tail).2 := by
  induction rows with
  | nil => simp [BinaryPRGRequestRulers.tripleWithTrace,Bounded,BinaryPRGHeapPrimitiveLifetime.cells,listCells,arraySlots]
  | cons item rest ih =>
      exact prefix_one _ _ 1 (by simp [BinaryPRGHeapPrimitiveLifetime.cells,listCells,arraySlots]) ih

theorem choice_bound {α : Type*} (rows : List α) (ruler : List Bool) : Bounded (BinaryPRGRequestRulers.choiceWithTrace rows ruler).2 := by
  apply wrapList_bound 3000 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨triple_bound _ _,triple_bound _ _⟩

theorem precision_ruler_bound (accuracy : BinaryAccuracyRulerReadWork.Prepared) : Bounded (BinaryPRGRequestRulers.precisionWithTrace accuracy).2 := by
  apply wrapList_bound 5 64 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨shifted_bound _ _,ruler_prepare_bound _ _,false_map_bound _⟩

theorem assemble_bound {n : ℕ} (checked : {prepared : BinaryPRGPreparation.Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n)
    (rows : List SignedWord) (hRows : rows.length = n) :
    Bounded (BinaryPRGRequestRulers.assembleWithRows checked accuracy header rows hRows).2 := by
  apply wrapList_bound n 64 (n+4) _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨precision_ruler_bound _,choice_bound _ _⟩

end Blotto.BinaryInputParserTraceSparsity
