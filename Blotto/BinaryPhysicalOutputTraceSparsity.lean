import Blotto.BinaryArithmeticTraceSparsity
import Blotto.BinaryPhysicalOutputMeasured
import Blotto.BinaryPRGGlobalFallbackMeasured

/-! Unconditional event certificates for the actual physical output producer.
The erasure bridges below preserve the full data/trace record. -/
namespace Blotto.BinaryPhysicalOutputTraceSparsity
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization
open BinaryMeasuredTraceSparsity
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem append_bound (first second : List Bool) :
    Bounded (BinaryHeapTapeMeasured.append first second).1.2 := by
  rw [BinaryHeapTapeMeasured.append_erases]
  exact of_sparse _ (BinaryInitialTraceSparsity.append_sparse first second)

theorem references_bound (pointers : List BinaryPRGWordStoreHeap.Pointer) :
    Bounded (BinaryReferenceVectorLifetime.encodeWithTrace pointers).2 := by
  induction pointers with
  | nil => exact wrap_bound 8 1 [] (by simp) (by decide)
  | cons pointer rest ih =>
      apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simp only [List.forall_mem_cons,children_nil,and_true]
      exact ⟨of_sparse _ (BinaryInitialTraceSparsity.field_sparse pointer),ih,
        of_sparse _ (BinaryInitialTraceSparsity.append_sparse _ _)⟩

theorem words_bound (heap : BinaryPRGWordStoreHeap.Heap) (words : List SignedWord) :
    Bounded (BinaryWordObjectArrayLifetime.wordsWithTrace heap words).2 := by
  induction words generalizing heap with
  | nil => exact wrap_bound 8 1 [] (by simp) (by decide)
  | cons word rest ih =>
      apply wrapList_bound 1 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simp only [List.forall_mem_cons,children_nil,and_true]
      exact ⟨of_sparse _ (BinaryInitialTraceSparsity.allocate_sparse _ _),ih _⟩

theorem prepare_bound (words : List SignedWord) :
    Bounded (BinaryWordObjectArrayMeasured.prepare words).1.2 := by
  rw [BinaryWordObjectArrayMeasured.prepare_erases]
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨words_bound _ _,references_bound _⟩

theorem read_bound {n : ℕ} (store : BinaryWordObjectArray.Store n) (index : List Bool) :
    Bounded (BinaryWordObjectArrayAccessMeasured.get store index).1.2 := by
  rw [BinaryWordObjectArrayAccessMeasured.get_erases]
  exact of_sparse _ (BinaryInitialTraceSparsity.object_get_sparse store index)

theorem indices_bound {α : Type*} (items : List α) :
    Bounded (BooleanArrayIndexMeasured.enumerate items).1.2 := by
  rw [BooleanArrayIndexMeasured.enumerate_erases]
  exact of_sparse _ (BinaryInitialTraceSparsity.indices_sparse items)

theorem ruler_bound (bits : List Bool) : Bounded (BinaryTapeFrameMeasured.ruler bits).1.2 := by
  induction bits with
  | nil => exact wrap_bound 8 1 [] (by simp) (by decide)
  | cons bit rest ih =>
      apply wrap_bound 16 1 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simpa only [List.forall_mem_cons,children_nil,and_true] using ih

theorem payload_bound (bits : List Bool) : Bounded (BinaryTapeFrameMeasured.payload bits).1.2 := by
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨ruler_bound _,append_bound _ _⟩

theorem word_bound (word : SignedWord) : Bounded (BinaryTapeFrameMeasured.word word).1.2 := by
  apply wrap_bound 48 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨payload_bound _,payload_bound _,append_bound _ _⟩

theorem emit_bound {n : ℕ} (store : BinaryWordObjectArray.Store n) (budget : SignedWord)
    (indices : List (List Bool)) : Bounded (BinaryPhysicalOutputMeasured.emit store budget indices).1.2 := by
  induction indices with
  | nil => exact wrap_bound 16 1 [] (by simp) (by decide)
  | cons index indices ih =>
      simp only [BinaryPhysicalOutputMeasured.emit_nil,BinaryPhysicalOutputMeasured.emit_cons]
      split
      · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
        simpa only [List.forall_mem_cons,children_nil,and_true] using read_bound store index
      · split
        · apply wrap_bound 64 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
          simp only [List.forall_mem_cons,children_nil,and_true]
          exact ⟨read_bound _ _,(by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),word_bound _,ih⟩
        · apply wrap_bound 64 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
          simp only [List.forall_mem_cons,children_nil,and_true]
          exact ⟨read_bound _ _,(by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),word_bound _,ih,
            append_bound _ _⟩

theorem output_bound (budget : SignedWord) (header : List Bool) (words : List SignedWord) :
    Bounded (BinaryPhysicalOutputMeasured.output budget header words).1.2 := by
  rw [BinaryPhysicalOutputMeasured.output_record]
  apply wrap_bound 64 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨prepare_bound _,indices_bound _,emit_bound _ _ _,append_bound _ _⟩

theorem output_length_usage (budget : SignedWord) (header : List Bool) (words : List SignedWord) :
    (BinaryPhysicalOutputMeasured.output budget header words).1.2.length ≤
      3*usage (BinaryPhysicalOutputMeasured.output budget header words).1.2+3 :=
  length_usage _ (output_bound budget header words)

theorem fallback_bound {n : ℕ} (input : BinaryLottoResourceInput.Input n) :
    Bounded (BinaryPRGGlobalFallbackMeasured.prepare input).1.2 :=
  measured_build n _ (fun _ => wrap_bound 8 1 [] (by simp) (by decide))

theorem fallback_length_usage {n : ℕ} (input : BinaryLottoResourceInput.Input n) :
    (BinaryPRGGlobalFallbackMeasured.prepare input).1.2.length ≤
      3*usage (BinaryPRGGlobalFallbackMeasured.prepare input).1.2+3 :=
  length_usage _ (fallback_bound input)

end Blotto.BinaryPhysicalOutputTraceSparsity
