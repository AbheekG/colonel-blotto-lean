import Blotto.BinaryFourFactoryTraceSparsity
import Blotto.BinaryNestedProfileMeasured

/-! Complete-trace event certificates for the nested reflected controller's
reference packing, parameter preparation and boundary/interior classification. -/
namespace Blotto.BinaryNestedControlTraceSparsity
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization
open BinaryStoredOverlapEnvironment
open BinaryMeasuredTraceSparsity
set_option autoImplicit false
set_option maxHeartbeats 4000000
abbrev Input := BinaryNestedParameters.Input

theorem pad_bound (table : Segment 3 9) : Bounded (BinaryNestedReferenceMeasured.pad table).1.2 := by
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨BinaryFactoryTraceSparsity.references_bound _ _,BinaryFactoryTraceSparsity.references_bound _ _,
    BinaryFactoryTraceSparsity.references_bound _ _⟩

theorem swap_rows_bound (rows : FixedArrayTable 18 (FixedArrayTable 3 SignedWord)) :
    Bounded (BinaryNestedReferenceMeasured.swapRows rows).1.2 :=
  measured_build 18 _ (fun _ => BinaryFactoryTraceSparsity.references_bound _ _)

theorem swap_bound (table : Segment 3 18) : Bounded (BinaryNestedReferenceMeasured.swap table).1.2 := by
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨swap_rows_bound _,swap_rows_bound _⟩

theorem restore_bound {α : Type*} (ordered : Bool) (prior : (α × Trace) × ℕ)
    (child : (Segment 3 18 × Trace) × ℕ) (hPrior : Bounded prior.1.2) (hChild : Bounded child.1.2) :
    Bounded (BinaryNestedReferenceMeasured.restore ordered prior child).1.2 := by
  unfold BinaryNestedReferenceMeasured.restore
  split
  · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨hPrior,hChild⟩
  · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨hPrior,hChild,swap_bound _⟩

theorem parameters_at_bound (input : Input) (x : SignedWord) : Bounded (BinaryNestedParameterMeasured.prepareAt input x).1.2 := by
  rw [BinaryNestedParameterMeasured.prepareAt_record,BinaryNestedParameterMeasured.runPrograms_record]
  apply wrap_bound 128 10 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨BinaryFactoryTraceSparsity.references_bound _ _,measured_build 9 _ (fun _ => BinaryFactoryTraceSparsity.syntax_bound _ _)⟩

theorem parameters_bound (input : Input) : Bounded (BinaryNestedParameterMeasured.prepare input).1.2 := by
  rw [BinaryNestedParameterMeasured.prepare_record]
  exact (
    parameters_at_bound _ _
  )

theorem geometry_bound (input : Input) (x : SignedWord) : Bounded (BinaryNestedParameterMeasured.geometry input x).1.2 := by
  rw [BinaryNestedParameterMeasured.geometry_record,BinaryNestedParameterMeasured.runPrograms_record]
  apply wrap_bound 96 8 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨BinaryFactoryTraceSparsity.references_bound _ _,measured_build 4 _ (fun _ => BinaryFactoryTraceSparsity.syntax_bound _ _)⟩

theorem row_shift_bound (row : FixedArrayTable 3 SignedWord) (x : SignedWord) :
    Bounded (BinaryNestedFirstAssemblyMeasured.rowShift row x).1.2 := by
  rw [BinaryNestedFirstAssemblyMeasured.rowShift_record]
  apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨(by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),BinaryFactoryTraceSparsity.references_bound _ _⟩

theorem rows_shift_bound (rows : FixedArrayTable 9 (FixedArrayTable 3 SignedWord)) (x : SignedWord) :
    Bounded (BinaryNestedFirstAssemblyMeasured.rowsShift rows x).1.2 := by
  rw [BinaryNestedFirstAssemblyMeasured.rowsShift_record]
  exact (
    measured_build 9 _ (fun _ => row_shift_bound _ _)
  )

theorem shift_bound (table : Segment 3 9) (x : SignedWord) : Bounded (BinaryNestedFirstAssemblyMeasured.shift table x).1.2 := by
  rw [BinaryNestedFirstAssemblyMeasured.shift_record]
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨rows_shift_bound _ _,rows_shift_bound _ _⟩

theorem boundary_child_bound (input : BinaryThreeInputCompiler.Input) : Bounded (BinaryNestedBoundaryMeasured.child input).1.2 := by
  rw [BinaryNestedBoundaryMeasured.child_record]
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨BinaryFactoryTraceSparsity.descriptor_bound _,pad_bound _⟩

theorem boundary_bound (input : Input) : Bounded (BinaryNestedBoundaryMeasured.boundary input).1.2 := by
  simp only [BinaryNestedBoundaryMeasured.boundary_record]
  unfold BinaryNestedBoundaryMeasured.choose

  split
  · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨BinaryArithmeticTraceSparsity.comparison_bound _ _,boundary_child_bound _⟩
  · dsimp only
    split
    · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simp only [List.forall_mem_cons,children_nil,and_true]
      exact ⟨BinaryArithmeticTraceSparsity.comparison_bound _ _,BinaryArithmeticTraceSparsity.comparison_bound _ _,boundary_child_bound _⟩
    · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simp only [List.forall_mem_cons,children_nil,and_true]
      exact ⟨BinaryArithmeticTraceSparsity.comparison_bound _ _,BinaryArithmeticTraceSparsity.comparison_bound _ _⟩

theorem order_bound (input : Input) : Bounded (BinaryNestedOrderMeasured.order input).1.2 := by
  rw [BinaryNestedOrderMeasured.order_record]
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨BinaryArithmeticTraceSparsity.comparison_bound _ _,(by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),
    (by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _)⟩

theorem regime_bound (input : Input) (parameters : FixedArrayTable 9 SignedWord) :
    Bounded (BinaryNestedRegimeMeasured.select input parameters).1.2 := by
  unfold BinaryNestedRegimeMeasured.select
  dsimp only
  split
  · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using BinaryArithmeticTraceSparsity.comparison_bound _ _
  · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨BinaryArithmeticTraceSparsity.comparison_bound _ _,BinaryArithmeticTraceSparsity.comparison_bound _ _⟩

theorem classify_bound (input : Input) : Bounded (BinaryNestedControlMeasured.classify input).1.2 := by
  simp only [BinaryNestedControlMeasured.classify_record]

  split
  · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using boundary_bound input
  · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨boundary_bound _,order_bound _⟩

theorem interior_bound (input : Input) : Bounded (BinaryNestedControlMeasured.interior input).1.2 := by
  simp only [BinaryNestedControlMeasured.interior_record]

  split
  · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using classify_bound input
  · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨classify_bound _,parameters_bound _⟩

theorem control_bound (input : Input) : Bounded (BinaryNestedControlMeasured.run input).1.2 := by
  simp only [BinaryNestedControlMeasured.run_record]

  split
  · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using interior_bound input
  · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨interior_bound _,regime_bound _ _⟩

end Blotto.BinaryNestedControlTraceSparsity
