import Blotto.BinaryArithmeticTraceSparsity
import Blotto.BinaryGroupFactoryMeasured

/-! Event certificates for the actual compiled regular/exceptional three-word
factories and their measured array builders. All original orderings are covered. -/
namespace Blotto.BinaryFactoryTraceSparsity
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization
open BinaryStoredOverlapEnvironment BinaryThreeInputCompiler BinaryGroupInputs BinaryGroupSamplers
open BinaryMeasuredTraceSparsity
open BinaryPRGHeapPrimitiveLifetime (cells)
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem syntax_bound {k : ℕ} (env : FixedArrayTable k SignedWord) (source : BinaryExpressionCompiler.Syntax k) :
    Bounded (BinaryQuadraticSyntaxMeasured.run env source).1.2 := by
  exact prefix_two _ _ _ 2 2 (by simp [cells,listCells,arraySlots])
    (by simp [BinaryQuadraticSyntaxMeasured.compileWithTrace,Bounded,cells,listCells,arraySlots])
    (BinaryArithmeticTraceSparsity.expression_bound _ _)

theorem references_bound {α : Type*} (n : ℕ) (f : Fin n → α) :
    Bounded (BinaryThreeReferenceMeasured.references n f).1.2 := by
  exact measured_build n _ (fun _ => wrap_bound 8 1 [] (by simp) (by decide))

theorem rows_bound {m : ℕ} (f : Fin 9 → Fin m → SignedWord) :
    Bounded (BinaryThreeReferenceMeasured.rows f).1.2 :=
  measured_build 9 _ (fun _ => references_bound _ _)

theorem assemble_bound {m : ℕ} (first second : Fin m → SignedWord) :
    Bounded (BinaryThreeReferenceMeasured.assemble first second).1.2 := by
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨references_bound _ _,rows_bound _,rows_bound _⟩

theorem exceptional_bound (input : Input) : Bounded (BinaryThreeReferenceMeasured.exceptional input).1.2 :=
  assemble_bound _ _

theorem swap_bound (segment : Segment 3 9) : Bounded (BinaryThreeReferenceMeasured.swap segment).1.2 := by
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨rows_bound _,rows_bound _⟩

theorem uniform_pair_bound (input : UniformInput 2) : Bounded (BinaryThreeReferenceMeasured.uniformPair input).1.2 :=
  assemble_bound _ _

theorem environment_bound (input : Input) : Bounded (BinaryThreeGeometryMeasured.environment input).1.2 :=
  references_bound _ _

theorem geometry_bound (env : FixedArrayTable 5 SignedWord) : Bounded (BinaryThreeGeometryMeasured.geometry env).1.2 := by
  rw [BinaryThreeGeometryMeasured.geometry_record]
  exact (
    measured_build 4 _ (fun _ => syntax_bound _ _)
  )

theorem regime_bound (env : FixedArrayTable 5 SignedWord) : Bounded (BinaryThreeGeometryMeasured.regime env).1.2 := by
  rw [BinaryThreeGeometryMeasured.regime_record]
  exact (
    syntax_bound _ _
  )

theorem vertex_row_bound (env : FixedArrayTable 4 SignedWord) (i : Fin 6) :
    Bounded (BinaryQuadraticThreeFactoryMeasured.vertexRow env i).1.2 := by
  rw [BinaryQuadraticThreeFactoryMeasured.vertexRow_record]
  exact (
    measured_build 3 _ (fun _ => syntax_bound _ _)
  )

theorem regular_bound (env : FixedArrayTable 4 SignedWord) :
    Bounded (BinaryQuadraticThreeFactoryMeasured.descriptor env).1.2 := by
  rw [BinaryQuadraticThreeFactoryMeasured.descriptor_record]
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨measured_build 9 _ (fun _ => syntax_bound _ _),
    measured_build 9 _ (fun _ => vertex_row_bound _ _),measured_build 9 _ (fun _ => vertex_row_bound _ _)⟩

theorem ordered_bound (input : Input) : Bounded (BinaryThreeFactoryMeasured.ordered input).1.2 := by
  simp only [BinaryThreeFactoryMeasured.ordered_record]

  split
  · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨environment_bound _,regime_bound _,BinaryArithmeticTraceSparsity.comparison_bound _ _,geometry_bound _,regular_bound _⟩
  · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨environment_bound _,regime_bound _,BinaryArithmeticTraceSparsity.comparison_bound _ _,exceptional_bound _⟩

theorem restore_bound (order : (Bool × Trace) × ℕ) (child : (Segment 3 9 × Trace) × ℕ)
    (hOrder : Bounded order.1.2) (hChild : Bounded child.1.2) :
    Bounded (BinaryThreeFactoryMeasured.restore order child).1.2 := by
  unfold BinaryThreeFactoryMeasured.restore
  split
  · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨hOrder,hChild⟩
  · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨hOrder,hChild,swap_bound _⟩

theorem descriptor_bound (input : Input) : Bounded (BinaryThreeFactoryMeasured.descriptor input).1.2 := by
  rw [BinaryThreeFactoryMeasured.descriptor_record]
  exact (
    restore_bound _ _ (BinaryArithmeticTraceSparsity.comparison_bound _ _) (ordered_bound _)
  )

theorem uniform_factory_bound {m : ℕ} (input : UniformInput m) (hm : m = 2 ∨ m = 3) :
    Bounded (BinaryGroupFactoryMeasured.uniformFactory input hm).1.2 := by
  rw [BinaryGroupFactoryMeasured.uniformFactory_record]
  rcases hm with rfl | rfl
  · change Bounded (wrap 64 4 [(BinaryThreeReferenceMeasured.uniformPair input).1.2])
    apply wrap_bound 64 4 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using uniform_pair_bound input
  · change Bounded (wrap 64 4 [(BinaryThreeFactoryMeasured.descriptor (BinaryGroupInputs.uniformThree input)).1.2])
    apply wrap_bound 64 4 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using descriptor_bound _

theorem uniform_prepared_bound {m : ℕ} (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) :
    Bounded (BinaryGroupFactoryMeasured.uniformPrepared input hC hAd hm).1.2 := by
  rw [BinaryGroupFactoryMeasured.uniformPrepared_record]
  apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simpa only [List.forall_mem_cons,children_nil,and_true] using uniform_factory_bound input hm

theorem mixed_prepared_bound (input : MixedInput 2) (hC : input.Canonical) (hAd : MixedAdmissible input) :
    Bounded (BinaryGroupFactoryMeasured.mixedTwoPrepared input hC hAd).1.2 := by
  rw [BinaryGroupFactoryMeasured.mixedTwoPrepared_record]
  apply wrap_bound 64 4 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simpa only [List.forall_mem_cons,children_nil,and_true] using descriptor_bound _

end Blotto.BinaryFactoryTraceSparsity
