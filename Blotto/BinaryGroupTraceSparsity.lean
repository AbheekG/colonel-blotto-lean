import Blotto.BinaryFactoryTraceSparsity
import Blotto.BinarySegmentTraceSparsity
import Blotto.BinaryWordTerminalCompleteMeasured

/-! Event certificates for measured uniform/mixed-two group draws and complete
route emission. Four-word/reflected dispatch remains a separate dependency. -/
namespace Blotto.BinaryGroupTraceSparsity
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization
open BinaryGroupInputs BinaryGroupSamplers
open BinaryMeasuredTraceSparsity
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem uniform_draw_bound {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryWordGroupDrawMeasured.uniformRun store input hC hAd hm K scalar pc hp).1.2 := by
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨BinaryFactoryTraceSparsity.uniform_prepared_bound _ _ _ _,BinarySegmentTraceSparsity.segment_bound _ _ _ _ _ _ _⟩

theorem mixed_draw_bound (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryWordGroupDrawMeasured.mixedTwoRun store input hC hAd K scalar pc hp).1.2 := by
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨BinaryFactoryTraceSparsity.mixed_prepared_bound _ _ _,BinarySegmentTraceSparsity.segment_bound _ _ _ _ _ _ _⟩

theorem cell_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) (j : Fin n) : Bounded (BinaryGroupEmissionMeasured.cell routes row j).1.2 := by
  simp only [BinaryGroupEmissionMeasured.cell_record]
  split
  · exact wrap_bound 8 1 [] (by simp) (by decide)
  · exact (by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _)

theorem emit_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) : Bounded (BinaryGroupEmissionMeasured.emit routes row).1.2 := by
  rw [BinaryGroupEmissionMeasured.emit_record]
  exact measured_build n _ (cell_bound routes row)

theorem subrow_bound {m : ℕ} (row : FixedArrayTable (m+1) SignedWord) :
    Bounded (BinaryGroupEmissionMeasured.subrow row).1.2 :=
  measured_build m _ (fun _ => wrap_bound 8 1 [] (by simp) (by decide))

theorem replace_bound {n : ℕ} (row : FixedArrayTable n SignedWord) (pivot : Fin n) (word : SignedWord) :
    Bounded (BinaryGroupEmissionMeasured.replace row pivot word).1.2 :=
  measured_build n _ (fun _ => wrap_bound 8 1 [] (by simp) (by decide))

theorem emit_mixed_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (row : FixedArrayTable (m+1) SignedWord) : Bounded (BinaryGroupEmissionMeasured.emitMixed routes pivot row).1.2 := by
  rw [BinaryGroupEmissionMeasured.emitMixed_record]
  apply wrap_bound 64 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨subrow_bound _,emit_bound _ _,(by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _),replace_bound _ _ _⟩

theorem emit_option_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : Option (FixedArrayTable m SignedWord)) : Bounded (BinaryGroupEmissionMeasured.emitOption routes row).1.2 := by
  rw [BinaryGroupEmissionMeasured.emitOption_record]
  cases row with
  | none => exact wrap_bound 8 1 [] (by simp) (by decide)
  | some row =>
      apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simpa only [List.forall_mem_cons,children_nil,and_true] using emit_bound routes row

theorem emit_mixed_option_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (row : Option (FixedArrayTable (m+1) SignedWord)) :
    Bounded (BinaryGroupEmissionMeasured.emitMixedOption routes pivot row).1.2 := by
  rw [BinaryGroupEmissionMeasured.emitMixedOption_record]
  cases row with
  | none => exact wrap_bound 8 1 [] (by simp) (by decide)
  | some row =>
      apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simpa only [List.forall_mem_cons,children_nil,and_true] using emit_mixed_bound routes pivot row

theorem collect_bound {n m : ℕ} (store : BinarySeedLookupTree.Store)
    (drawn : (BinaryPRGWordControllerTerminal.Result store m × Trace) × ℕ)
    (emitted : (Option (FixedArrayTable n SignedWord) × Trace) × ℕ)
    (hDraw : Bounded drawn.1.2) (hEmit : Bounded emitted.1.2) :
    Bounded (BinaryWordGroupCompleteMeasured.collect store drawn emitted).1.2 := by
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨hDraw,hEmit⟩

theorem after_mixed_bound {n m : ℕ} (store : BinarySeedLookupTree.Store)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (drawn : (BinaryPRGWordControllerTerminal.Result store (m+1) × Trace) × ℕ) (hDraw : Bounded drawn.1.2) :
    Bounded (BinaryWordGroupCompleteMeasured.afterMixed store routes pivot drawn).1.2 :=
  collect_bound _ _ _ hDraw (emit_mixed_option_bound _ _ _)

theorem uniform_complete_bound {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryWordGroupCompleteMeasured.uniformRun store input hC hAd hm routes K scalar pc hp).1.2 :=
  collect_bound _ _ _ (uniform_draw_bound _ _ _ _ _ _ _ _ _) (emit_option_bound _ _)

theorem mixed_two_complete_bound {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 2)) (pivot : Fin n)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryWordGroupCompleteMeasured.mixedTwoRun store input hC hAd routes pivot K scalar pc hp).1.2 :=
  after_mixed_bound _ _ _ _ (mixed_draw_bound _ _ _ _ _ _ _ _)

theorem branch_bound {α : Type*} (drawn : (α × Trace) × ℕ) (hDraw : Bounded drawn.1.2) :
    Bounded (BinaryWordTerminalCompleteMeasured.branch drawn).1.2 := by
  apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simpa only [List.forall_mem_cons,children_nil,and_true] using hDraw

end Blotto.BinaryGroupTraceSparsity
