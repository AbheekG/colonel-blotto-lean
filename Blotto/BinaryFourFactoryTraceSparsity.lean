import Blotto.BinaryFactoryTraceSparsity
import Blotto.BinarySegmentTraceSparsity
import Blotto.BinaryFourOrderedMeasured
import Blotto.BinaryFourOrderMeasured

/-! Event certificates for actual ordering, gluing and small uniform factories.
The reflected recursive branch is not covered by this component module. -/
namespace Blotto.BinaryFourFactoryTraceSparsity
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization
open BinaryStoredOverlapEnvironment
open BinaryMeasuredTraceSparsity
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem compare_bound (length : Fin 3 → SignedWord) (i j : Fin 3) :
    Bounded (BinaryFourOrderMeasured.compare length i j).1.2 := by
  apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simpa only [List.forall_mem_cons,children_nil,and_true] using BinaryArithmeticTraceSparsity.comparison_bound _ _

theorem sort_bound (length : Fin 3 → SignedWord) : Bounded (BinaryFourOrderMeasured.sort length).1.2 := by
  apply wrap_bound 32 3 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨compare_bound _ _ _,compare_bound _ _ _,compare_bound _ _ _⟩

theorem order_bound (input : BinaryFourSpecSampler.Input) : Bounded (BinaryFourOrderMeasured.ordered input).1.2 := by
  apply wrap_bound 64 4 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simpa only [List.forall_mem_cons,children_nil,and_true] using sort_bound _

theorem guard_bound (input : BinaryFourParameters.Input) : Bounded (BinaryFourGuardMeasured.guard input).1.2 := by
  rw [BinaryFourGuardMeasured.guard_record]
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨(by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),
    (by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),BinaryArithmeticTraceSparsity.comparison_bound _ _⟩

theorem parameters_bound (input : BinaryFourParameters.Input) : Bounded (BinaryFourParametersMeasured.prepare input).1.2 := by
  rw [BinaryFourParametersMeasured.prepare_record]
  apply wrap_bound 114 10 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨BinaryFactoryTraceSparsity.references_bound _ _,measured_build 8 _ (fun _ => BinaryFactoryTraceSparsity.syntax_bound _ _)⟩

theorem parents_bound (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    Bounded (BinaryFourGluingParentsMeasured.run input hC).1.2 := by
  rw [BinaryFourGluingParentsMeasured.run_record]
  apply wrap_bound 64 4 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨parameters_bound _,BinaryFactoryTraceSparsity.descriptor_bound _,BinaryFactoryTraceSparsity.descriptor_bound _⟩

theorem overlap_environment_bound {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) :
    Bounded (BinaryOverlapGluingMeasured.environment first second interval budget i j).1.2 :=
  BinaryFactoryTraceSparsity.references_bound _ _

theorem overlap_from_environment_bound (env : (FixedArrayTable 16 SignedWord × Trace) × ℕ) (hEnv : Bounded env.1.2) :
    Bounded (BinaryOverlapGluingMeasured.fromEnvironment env).1.2 := by
  rw [BinaryOverlapGluingMeasured.fromEnvironment_record]
  apply wrap_bound 64 4 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨hEnv,BinaryFactoryTraceSparsity.syntax_bound _ _,
    measured_build 4 _ (fun _ => BinaryFactoryTraceSparsity.syntax_bound _ _),
    measured_build 4 _ (fun _ => BinaryFactoryTraceSparsity.syntax_bound _ _)⟩

theorem overlap_slot_bound {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) :
    Bounded (BinaryOverlapGluingMeasured.slot first second interval budget i j).1.2 := by
  rw [BinaryOverlapGluingMeasured.slot_record]
  exact (
    overlap_from_environment_bound _ (overlap_environment_bound _ _ _ _ _ _)
  )

theorem overlap_bound {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h) (interval budget : SignedWord) :
    Bounded (BinaryOverlapGluingMeasured.descriptor first second interval budget).1.2 := by
  rw [BinaryOverlapGluingMeasured.descriptor_record]
  apply wrap_bound 64 4 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨measured_build (k*h) _ (fun _ => overlap_slot_bound _ _ _ _ _ _),
    BinaryFactoryTraceSparsity.references_bound _ _,BinaryFactoryTraceSparsity.references_bound _ _,BinaryFactoryTraceSparsity.references_bound _ _⟩

theorem gluing_bound (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    Bounded (BinaryFourGluingMeasured.descriptor input hC).1.2 := by
  rw [BinaryFourGluingMeasured.descriptor_record]
  apply wrap_bound 64 4 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨parents_bound _ _,overlap_bound _ _ _ _⟩

theorem split_arithmetic_bound (first second coordinate : SignedWord) :
    Bounded (BinarySmallUniformSplitMeasured.arithmetic first second coordinate).1.2 := by
  rw [BinarySmallUniformSplitMeasured.arithmetic_record]
  apply wrap_bound 32 6 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨(by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),(by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),
    (by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),(by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),
    (by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _)⟩

theorem split_bound (first second : SignedWord) (row : FixedArrayTable 3 SignedWord) :
    Bounded (BinarySmallUniformSplitMeasured.split first second row).1.2 := by
  rw [BinarySmallUniformSplitMeasured.split_record]
  apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨split_arithmetic_bound _ _ _,BinaryFactoryTraceSparsity.references_bound _ _⟩

theorem small_preparation_bound (input : BinaryFourParameters.Input) :
    Bounded (BinarySmallUniformPreparationMeasured.prepare input).1.2 := by
  rw [BinarySmallUniformPreparationMeasured.prepare_record]
  apply wrap_bound 48 4 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨parameters_bound _,(by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),
    (by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),(by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _)⟩

theorem small_child_bound (input : BinarySmallUniformCompiler.Input) :
    Bounded (BinarySmallUniformDescriptorMeasured.child input).1.2 := by
  rw [BinarySmallUniformDescriptorMeasured.child_record]
  apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simpa only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,List.forall_mem_cons,children_nil,and_true] using BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _

theorem small_descriptor_bound (input : BinarySmallUniformCompiler.Input) :
    Bounded (BinarySmallUniformDescriptorMeasured.descriptor input).1.2 := by
  rw [BinarySmallUniformDescriptorMeasured.descriptor_record]
  apply wrap_bound 64 4 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨small_child_bound _,BinaryFactoryTraceSparsity.descriptor_bound _,
    measured_build 9 _ (fun _ => split_bound _ _ _),measured_build 9 _ (fun _ => split_bound _ _ _)⟩

theorem small_factory_bound (input : BinaryFourParameters.Input) :
    Bounded (BinarySmallUniformFactoryMeasured.descriptor input).1.2 := by
  rw [BinarySmallUniformFactoryMeasured.descriptor_record]
  apply wrap_bound 64 3 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨small_preparation_bound _,small_descriptor_bound _⟩

theorem gluing_draw_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryGluingSampler.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryFourGluingDrawMeasured.run store input hC hAd K scalar pc hp).1.2 := by
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨gluing_bound _ _,BinarySegmentTraceSparsity.segment_bound _ _ _ _ _ _ _⟩

theorem small_uniform_draw_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryFourSmallUniformDrawMeasured.run store input hC hAd K scalar pc hp).1.2 := by
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨small_factory_bound _,BinarySegmentTraceSparsity.segment_bound _ _ _ _ _ _ _⟩

theorem small_coin_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryFourSmallCoinMeasured.sample store input pc hp).1.2 := by
  rw [BinaryFourSmallCoinMeasured.sample_record]
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  constructor
  · rw [BinaryQuadraticMeasured.canonicalize_erases]
    exact BinaryArithmeticTraceSparsity.canonicalize_bound _
  · exact BinaryCoinTraceSparsity.sample_bound _ _ _ _

end Blotto.BinaryFourFactoryTraceSparsity
