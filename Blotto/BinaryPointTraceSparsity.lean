import Blotto.BinaryPhysicalOutputTraceSparsity
import Blotto.BinaryPhysicalPointMeasured

/-! Physical interpolation and dyadic point traces. Allocation-free trimming
scans are paid by their actual preceding reverse-copy cells; no standalone
allocation certificate is asserted for such a scan. -/
namespace Blotto.BinaryPointTraceSparsity
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization
open BinaryMeasuredTraceSparsity
open BinaryPRGHeapPrimitiveLifetime (cells)
open BinaryResourceTraceLength (under_length)
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem drop_length (bits : List Bool) : (BinaryMidpointTapeLifetime.dropWithTrace bits).2.length ≤ bits.length+1 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      cases bit <;> simp only [BinaryMidpointTapeLifetime.dropWithTrace,List.length_append,under_length,
        List.length_cons,List.length_nil] <;> omega

theorem midpoint_trim_bound (bits : List Bool) : Bounded (BinaryMidpointTapeMeasured.trim bits).1.2 := by
  rw [BinaryMidpointTapeMeasured.trim_erases]
  have hd := drop_length (reverseWithTrace bits []).1
  have hf : (reverseWithTrace bits []).1.length = bits.length := by
    simp only [reverseWithTrace_result,List.reverseAux_eq,List.append_nil,List.length_reverse]
  rw [hf] at hd
  unfold Bounded BinaryMidpointTapeLifetime.trimWithTrace
  simp only [List.length_append,under_length,BinaryResourceTraceLength.reverse_trace_length,
    cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,reverseWithTrace_cells,
    reverseWithTrace_arrays,listCells,arraySlots,List.length_cons,List.length_nil]
  omega

theorem denominator_bound (bits : List Bool) : Bounded (BinaryMidpointTapeMeasured.denominator bits).1.2 := by
  induction bits with
  | nil => simp [BinaryMidpointTapeMeasured.denominator,Bounded,cells,listCells,arraySlots]
  | cons bit rest ih => exact prefix_one _ _ 1 (by simp [cells,listCells,arraySlots]) ih

theorem midpoint_bound (bits : List Bool) : Bounded (BinaryMidpointTapeMeasured.sample bits).1.2 := by
  exact prefix_two _ _ _ 2 2 (by simp [cells,listCells,arraySlots]) (midpoint_trim_bound _) (denominator_bound _)

theorem coordinate_bound (first second scalar : SignedWord) :
    Bounded (BinaryPhysicalInterpolationMeasured.coordinate first second scalar).1.2 := by
  simp only [BinaryPhysicalInterpolationMeasured.coordinate,BinaryNormalizedCoordinate.coordinate_record]
  apply wrap_bound 64 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨(by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),
    (by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),
    (by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),
    (by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _)⟩

theorem interpolation_loop_bound {n m : ℕ} (first : BinaryWordObjectArray.Store n)
    (second : BinaryWordObjectArray.Store m) (scalar : SignedWord) (indices : List (List Bool)) :
    Bounded (BinaryPhysicalInterpolationMeasured.loop first second scalar indices).1.2 := by
  induction indices with
  | nil => exact wrap_bound 16 1 [] (by simp) (by decide)
  | cons index rest ih =>
      rw [BinaryPhysicalInterpolationMeasured.loop_record]
      dsimp only
      split
      · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
        simpa only [List.forall_mem_cons,children_nil,and_true] using BinaryPhysicalOutputTraceSparsity.read_bound first index
      · split
        · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
          simp only [List.forall_mem_cons,children_nil,and_true]
          exact ⟨BinaryPhysicalOutputTraceSparsity.read_bound _ _,BinaryPhysicalOutputTraceSparsity.read_bound _ _⟩
        · apply wrapList_bound 1 64 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
          simp only [List.forall_mem_cons,children_nil,and_true]
          exact ⟨BinaryPhysicalOutputTraceSparsity.read_bound _ _,BinaryPhysicalOutputTraceSparsity.read_bound _ _,
            coordinate_bound _ _ _,ih⟩

theorem interpolation_bound (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length = q.length) :
    Bounded (BinaryPhysicalInterpolationMeasured.run scalar p q hLength).1.2 := by
  rw [BinaryPhysicalInterpolationMeasured.run_record]
  apply wrap_bound 64 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨BinaryPhysicalOutputTraceSparsity.prepare_bound _,BinaryPhysicalOutputTraceSparsity.prepare_bound _,
    BinaryPhysicalOutputTraceSparsity.indices_bound _,interpolation_loop_bound _ _ _ _⟩

theorem stage_bound (p q : List SignedWord) (bits : List Bool) (hLength : p.length = q.length) :
    Bounded (BinaryPhysicalPointMeasured.stage p q bits hLength).1.2 := by
  rw [BinaryPhysicalPointMeasured.stage_record]
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨midpoint_bound _,interpolation_bound _ _ _ _⟩

theorem point_bound {n k : ℕ} (table : BinaryStoredOverlapEnvironment.Segment n k) (slot : Fin k)
    (K : ℕ) (bits : BinaryScalarTape K) : Bounded (BinaryPhysicalPointMeasured.sample table slot K bits).1.2 := by
  rw [BinaryPhysicalPointMeasured.sample_record]
  apply wrapList_bound (2*n+K) 64 (2*n+K+4) _
    (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨stage_bound _ _ _ _,table_bound _⟩

end Blotto.BinaryPointTraceSparsity
