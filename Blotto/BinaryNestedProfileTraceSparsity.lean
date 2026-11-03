import Blotto.BinaryNestedControlTraceSparsity

/-! All three finite nested-profile regimes used by reflected terminal output
have event certificates on every typed input and selected scalar tape. -/
namespace Blotto.BinaryNestedProfileTraceSparsity
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization
open BinaryStoredOverlapEnvironment
open BinaryMeasuredTraceSparsity BinaryNestedControlTraceSparsity
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem location_bound (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    Bounded (BinaryNestedFirstLocationMeasured.location input K bits).1.2 := by
  rw [BinaryNestedFirstLocationMeasured.location_record]
  apply wrapList_bound K 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨BinaryPointTraceSparsity.midpoint_bound _,parameters_at_bound _ _⟩

theorem positive_descriptor_bound (input : Input) (x : SignedWord) :
    Bounded (BinaryNestedFirstDescriptorMeasured.positive input x).1.2 := by
  rw [BinaryNestedFirstDescriptorMeasured.positive_record,BinaryNestedFirstDescriptorMeasured.positiveFrom_record]
  apply wrap_bound 40 3 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨geometry_bound _ _,BinaryFactoryTraceSparsity.regular_bound _,shift_bound _ _⟩

theorem first_descriptor_bound (input : Input) (x : SignedWord) :
    Bounded (BinaryNestedFirstDescriptorMeasured.descriptor input x).1.2 := by
  simp only [BinaryNestedFirstDescriptorMeasured.fromParameters_record,BinaryNestedFirstDescriptorMeasured.descriptor_record]
  unfold BinaryNestedFirstDescriptorMeasured.finish
  dsimp only
  apply wrap_bound 40 3 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  refine ⟨parameters_at_bound _ _,BinaryArithmeticTraceSparsity.comparison_bound _ _,?_⟩
  split
  · exact positive_descriptor_bound _ _
  · exact BinaryFactoryTraceSparsity.assemble_bound _ _

theorem first_profile_bound (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    Bounded (BinaryNestedFirstProfileMeasured.profile input K bits).1.2 := by
  rw [BinaryNestedFirstProfileMeasured.profile_record]
  apply wrap_bound 40 3 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨location_bound _ _ _,first_descriptor_bound _ _,pad_bound _⟩

theorem family_preparation_bound (input : Input) (length : SignedWord) :
    Bounded (BinaryNestedFamilyMeasured.prepare input length).1.2 := by
  rw [BinaryNestedFamilyMeasured.prepare_record]
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simpa only [List.forall_mem_cons,children_nil,and_true] using parameters_at_bound input length

theorem family_bound (input : Input) (length : SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :
    Bounded (BinaryNestedFamilyMeasured.lottery input length K bits).1.2 := by
  rw [BinaryNestedFamilyMeasured.lottery_record,BinaryNestedFamilyMeasured.fromFamily_record]
  apply wrap_bound 40 3 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨family_preparation_bound _ _,location_bound _ _ _,first_descriptor_bound _ _⟩

theorem uniform_preparation_bound (input : Input) (mirror : SignedWord) :
    Bounded (BinaryNestedSecondUniformMeasured.prepare input mirror).1.2 := by
  rw [BinaryNestedSecondUniformMeasured.prepare_record]
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨(by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),(by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _)⟩

theorem uniform_bound (input : Input) (mirror : SignedWord) :
    Bounded (BinaryNestedSecondUniformMeasured.uniform input mirror).1.2 := by
  rw [BinaryNestedSecondUniformMeasured.uniform_record,BinaryNestedSecondUniformMeasured.fromPrepared_record]
  apply wrap_bound 40 3 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨uniform_preparation_bound _ _,BinaryFactoryTraceSparsity.ordered_bound _,shift_bound _ _⟩

theorem binary_weights_bound (p q : SignedWord) (first second : FixedArrayTable 9 SignedWord) :
    Bounded (BinaryNestedBinaryAssemblyMeasured.weights p q first second).1.2 := by
  rw [BinaryNestedBinaryAssemblyMeasured.weights_record]
  apply measured_build 18
  intro slot
  refine Fin.addCases (m := 9) (n := 9) (fun j => ?_) (fun j => ?_) slot <;>
    simp only [Fin.addCases_left,Fin.addCases_right] <;> exact (by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _)

theorem binary_bound (p : SignedWord) (first second : Segment 3 9) :
    Bounded (BinaryNestedBinaryAssemblyMeasured.binary p first second).1.2 := by
  rw [BinaryNestedBinaryAssemblyMeasured.binary_record,BinaryNestedBinaryAssemblyMeasured.fromComplement_record]
  apply wrap_bound 40 3 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨(by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),binary_weights_bound _ _ _ _,
    BinaryFactoryTraceSparsity.references_bound _ _,BinaryFactoryTraceSparsity.references_bound _ _⟩

theorem second_mix_bound (alpha : SignedWord) (family : Segment 3 9) (uniform : (Segment 3 9 × Trace) × ℕ)
    (hUniform : Bounded uniform.1.2) : Bounded (BinaryNestedSecondProfileMeasured.mix alpha family uniform).1.2 := by
  rw [BinaryNestedSecondProfileMeasured.mix_record]
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨hUniform,binary_bound _ _ _⟩

theorem second_profile_bound (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :
    Bounded (BinaryNestedSecondProfileMeasured.profile input parameters K bits).1.2 := by
  simp only [BinaryNestedSecondProfileMeasured.profile_record]
  unfold BinaryNestedSecondProfileMeasured.finish

  apply wrap_bound 40 3 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  refine ⟨family_bound _ _ _ _,BinaryArithmeticTraceSparsity.comparison_bound _ _,?_⟩
  split
  · exact second_mix_bound _ _ _ (uniform_bound _ _)
  · exact pad_bound _

theorem residual_vertex_bound (env : FixedArrayTable 5 SignedWord) (vertex : Fin 3) :
    Bounded (BinaryNestedResidualDescriptorMeasured.vertexRow env vertex).1.2 := by
  rw [BinaryNestedResidualDescriptorMeasured.vertexRow_record]
  exact (
    measured_build 3 _ (fun _ => BinaryFactoryTraceSparsity.syntax_bound _ _)
  )

theorem residual_rows_bound (env : FixedArrayTable 5 SignedWord) (edge : Fin 3 → Fin 3) :
    Bounded (BinaryNestedResidualDescriptorMeasured.rows env edge).1.2 := by
  rw [BinaryNestedResidualDescriptorMeasured.rows_record]
  exact (
    measured_build 3 _ (fun _ => residual_vertex_bound _ _)
  )

theorem residual_descriptor_bound (env : FixedArrayTable 5 SignedWord) :
    Bounded (BinaryNestedResidualDescriptorMeasured.descriptor env).1.2 := by
  rw [BinaryNestedResidualDescriptorMeasured.descriptor_record,BinaryNestedResidualDescriptorMeasured.weights_record]
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨measured_build 3 _ (fun _ => BinaryFactoryTraceSparsity.syntax_bound _ _),residual_rows_bound _ _,residual_rows_bound _ _⟩

theorem residual_environment_bound (input : Input) (parameters : FixedArrayTable 9 SignedWord) :
    Bounded (BinaryNestedResidualMeasured.environment input parameters).1.2 := by
  rw [BinaryNestedResidualMeasured.environment_record]
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨(by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),BinaryFactoryTraceSparsity.references_bound _ _⟩

theorem residual_bound (input : Input) (parameters : FixedArrayTable 9 SignedWord) :
    Bounded (BinaryNestedResidualMeasured.residual input parameters).1.2 := by
  rw [BinaryNestedResidualMeasured.residual_record,BinaryNestedResidualMeasured.fromEnvironment_record]
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨residual_environment_bound _ _,residual_descriptor_bound _⟩

theorem residual_pad_bound (table : Segment 3 3) : Bounded (BinaryNestedResidualMeasured.pad table).1.2 := by
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨BinaryFactoryTraceSparsity.references_bound _ _,BinaryFactoryTraceSparsity.references_bound _ _,
    BinaryFactoryTraceSparsity.references_bound _ _⟩

theorem third_mix_bound (alpha : SignedWord) (padded : Segment 3 9) (family : (Segment 3 9 × Trace) × ℕ)
    (hFamily : Bounded family.1.2) : Bounded (BinaryNestedThirdProfileMeasured.mix alpha padded family).1.2 := by
  rw [BinaryNestedThirdProfileMeasured.mix_record]
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨hFamily,binary_bound _ _ _⟩

theorem third_profile_bound (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :
    Bounded (BinaryNestedThirdProfileMeasured.profile input parameters K bits).1.2 := by
  simp only [BinaryNestedThirdProfileMeasured.profile_record]
  unfold BinaryNestedThirdProfileMeasured.finish

  apply wrap_bound 40 3 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  refine ⟨residual_bound _ _,residual_pad_bound _,BinaryArithmeticTraceSparsity.comparison_bound _ _,?_⟩
  split
  · exact third_mix_bound _ _ _ (family_bound _ _ _ _)
  · exact pad_bound _

theorem ordered_bound (input : Input) (parameters : FixedArrayTable 9 SignedWord) (regime : Fin 3)
    (K : ℕ) (bits : BinaryScalarTape K) : Bounded (BinaryNestedProfileMeasured.ordered input parameters regime K bits).1.2 := by
  simp only [BinaryNestedProfileMeasured.ordered_record]
  split
  · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using first_profile_bound input K bits
  · split
    · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simpa only [List.forall_mem_cons,children_nil,and_true] using second_profile_bound input parameters K bits
    · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simpa only [List.forall_mem_cons,children_nil,and_true] using third_profile_bound input parameters K bits

theorem profile_bound (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    Bounded (BinaryNestedProfileMeasured.profile input K bits).1.2 := by
  simp only [BinaryNestedProfileMeasured.profile_record]

  split
  · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using control_bound input
  · exact restore_bound _ _ _ (control_bound _) (ordered_bound _ _ _ _ _)

end Blotto.BinaryNestedProfileTraceSparsity
