import Blotto.BinaryLegacyNativeTraceSparsity
import Blotto.BinaryNestedProfileTraceSparsity
import Blotto.BinaryReflectedDrawMeasured

/-! Structural event certificates for the complete reflected execution,
including actual resource setup, every nested regime and reflected output. -/
namespace Blotto.BinaryReflectedTraceSparsity
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization BinaryRationalEncoding
open BinaryStoredOverlapEnvironment
open BinaryMeasuredTraceSparsity
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem system_bound (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord) :
    Bounded (BinaryReflectedSystemMeasured.fromParameters input parameters).1.2 := by
  rw [BinaryReflectedSystemMeasured.fromParameters_record]
  apply wrap_bound 192 8 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨BinaryFactoryTraceSparsity.references_bound _ _,(by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),
    measured_build 3 _ (fun _ => (by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _)),
    measured_build 3 _ (fun _ => (by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _))⟩

theorem capacity_bound (system : BinaryReflectedFourSetup.System) :
    Bounded (BinaryReflectedSystemMeasured.capacity system).1.2 := by
  rw [BinaryReflectedSystemMeasured.capacity_record]
  exact (
    measured_build 3 _ (fun _ => (by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _))
  )

theorem preparation_bound (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    Bounded (BinaryReflectedPreparationMeasured.prepare input hC).1.2 := by
  rw [BinaryReflectedPreparationMeasured.prepare_record,BinaryReflectedPreparationMeasured.fromParameters_record,BinaryReflectedPreparationMeasured.fromSystem_record]
  apply wrap_bound 48 4 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨BinaryFourFactoryTraceSparsity.parameters_bound _,system_bound _ _,capacity_bound _⟩

theorem fractional_bound (capacity resource : FixedArrayTable 3 SignedWord) (j : Fin 3) :
    Bounded (BinaryReflectedFocusMeasured.fractional capacity resource j).1.2 := by
  apply wrap_bound 12 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨BinaryArithmeticTraceSparsity.comparison_bound _ _,BinaryArithmeticTraceSparsity.comparison_bound _ _⟩

theorem focus_bound (capacity resource : FixedArrayTable 3 SignedWord) :
    Bounded (BinaryReflectedFocusMeasured.focus capacity resource).1.2 := by
  unfold BinaryReflectedFocusMeasured.focus
  dsimp only
  split
  · apply wrap_bound 12 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using fractional_bound capacity resource 0
  · apply wrap_bound 12 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨fractional_bound _ _ _,fractional_bound _ _ _⟩

theorem endpoint_bound (system : BinaryReflectedFourSetup.System) (state : BinaryThreeResourceState.State) (j : Fin 3) :
    Bounded (BinaryReflectedTerminalInputMeasured.endpoint system state j).1.2 := by
  apply wrap_bound 8 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  rw [BooleanFreshSeedMeasured.scan_erases]
  exact of_sparse _ (BinaryInitialTraceSparsity.scan_sparse _)

theorem terminal_input_bound {input : BinaryFourParameters.Input} (prepared : BinaryReflectedPreparationLifetime.Prepared input)
    (state : BinaryThreeResourceState.State) : Bounded (BinaryReflectedTerminalInputMeasured.terminal prepared state).1.2 := by
  rw [BinaryReflectedTerminalInputMeasured.terminal_record]
  apply wrap_bound 40 3 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨focus_bound _ _,endpoint_bound _ _ _,endpoint_bound _ _ _,(by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _)⟩

theorem permutation_rows_bound (values : FixedArrayTable 18 (FixedArrayTable 3 SignedWord)) (pi : Equiv.Perm (Fin 3)) :
    Bounded (BinaryTerminalPermutationMeasured.rows values pi).1.2 :=
  measured_build 18 _ (fun _ => BinaryFactoryTraceSparsity.references_bound _ _)

theorem permutation_bound (table : Segment 3 18) (pi : Equiv.Perm (Fin 3)) :
    Bounded (BinaryTerminalPermutationMeasured.permute table pi).1.2 := by
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨permutation_rows_bound _ _,permutation_rows_bound _ _⟩

theorem from_terminal_bound
    (terminal : ((BinaryNestedParameters.Input × Equiv.Perm (Fin 3)) × Trace) × ℕ)
    (K : ℕ) (outer : BinaryScalarTape K) (hTerminal : Bounded terminal.1.2) :
    Bounded (BinaryReflectedTerminalFactoryMeasured.fromTerminal terminal K outer).1.2 := by
  rw [BinaryReflectedTerminalFactoryMeasured.fromTerminal_record]
  apply wrap_bound 40 3 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨hTerminal,BinaryNestedProfileTraceSparsity.profile_bound _ _ _,permutation_bound _ _⟩

theorem table_bound {input : BinaryFourParameters.Input} (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (K : ℕ) (outer : BinaryScalarTape K) :
    Bounded (BinaryReflectedTerminalFactoryMeasured.table cached result K outer).1.2 := by
  rw [BinaryReflectedTerminalFactoryMeasured.table_record,BinaryReflectedTerminalFactoryMeasured.fromTerminal_record]
  exact (
    from_terminal_bound _ _ _ (terminal_input_bound _ _)
  )

theorem prepared_bound (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result) (K : ℕ) (outer : BinaryScalarTape K) :
    Bounded (BinaryReflectedTerminalFactoryMeasured.prepared input hC hAd cached N bits result hSuccess K outer).1.2  := by
  rw [BinaryReflectedTerminalFactoryMeasured.prepared_record]
  simpa only [BinaryReflectedTerminalFactoryMeasured.attach] using table_bound cached result K outer

theorem reflect_bound (input : BinaryFourParameters.Input) (row : FixedArrayTable 3 SignedWord) :
    Bounded (BinaryReflectedEmissionMeasured.reflect input row).1.2 := by
  rw [BinaryReflectedEmissionMeasured.reflect_record]
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨measured_build 3 _ (fun _ => (by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _)),
    BinaryFactoryTraceSparsity.references_bound _ _⟩

theorem emission_bound (input : BinaryFourParameters.Input) (table : Segment 3 18) (slot : Fin 18)
    (K : ℕ) (scalar : BinaryScalarTape K) : Bounded (BinaryReflectedEmissionMeasured.sample input table slot K scalar).1.2 := by
  rw [BinaryReflectedEmissionMeasured.sample_record]
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨BinaryPointTraceSparsity.point_bound _ _ _ _,reflect_bound _ _⟩

theorem table_draw_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (prepared : BinaryStoredSegmentProgram.Prepared 3 18) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryReflectedTableDrawMeasured.run store input prepared K scalar pc hp).1.2 := by
  rw [BinaryReflectedTableDrawMeasured.run_record]
  dsimp only
  split
  · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using BinarySegmentTraceSparsity.select_bound store prepared 0 pc hp
  · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨BinarySegmentTraceSparsity.select_bound _ _ _ _ _,emission_bound _ _ _ _ _⟩

theorem resource_draw_bound (seed : BinarySeedLookupTree.Store) {input : BinaryFourParameters.Input}
    (prepared : BinaryReflectedPreparationLifetime.Prepared input) (pc : FixedBinaryWord seed.width)
    (hp : pc.value ≤ seed.cap.value) : Bounded (BinaryReflectedResourceMeasured.draw seed prepared pc hp).1.2 := by
  apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  rw [BinaryReflectedNativeFused.native_previous]
  simpa only [List.forall_mem_cons,children_nil,and_true] using BinaryLegacyNativeTraceSparsity.native_bound
    seed prepared.capacity prepared.system.initial prepared.capacity_canonical prepared.canonical.2.2.2 pc hp

theorem resource_bound (seed : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    Bounded (BinaryReflectedResourceMeasured.run seed input hC pc hp).1.2 := by
  rw [BinaryReflectedResourceMeasured.run_record]
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨preparation_bound _ _,resource_draw_bound _ _ _ _⟩

theorem after_resource_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input)
    (hC : input.Canonical) (hAd : BinaryReflectedSerialRun.Admissible input) (cached : BinaryReflectedPreparationLifetime.Prepared input)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (resource : BinaryPRGWordControllerThreeResource.Result store (BinaryReflectedFourSetup.prepare input).capacity)
    (hResource : resource = BinaryPRGWordControllerThreeResource.setupIndexed store input hC pc hp)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    Bounded (BinaryReflectedDrawMeasured.afterResource store input hC hAd cached pc hp resource hResource K outer scalar).1.2 := by
  rw [BinaryReflectedDrawMeasured.afterResource_record]
  split
  · exact wrap_bound 24 2 [] (by simp) (by decide)
  · apply wrap_bound 40 3 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨prepared_bound _ _ _ _ _ _ _ _ _ _,table_draw_bound _ _ _ _ _ _ _⟩

theorem reflected_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryReflectedSerialRun.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryReflectedDrawMeasured.run store input hC hAd K outer scalar pc hp).1.2 := by
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨resource_bound _ _ _ _ _,after_resource_bound _ _ _ _ _ _ _ _ _ _ _ _⟩

end Blotto.BinaryReflectedTraceSparsity
