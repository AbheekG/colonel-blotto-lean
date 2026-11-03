import Blotto.BinaryCoinTraceSparsity
import Blotto.BinaryPointTraceSparsity
import Blotto.BinaryWordSegmentMeasured

/-! Unconditional event envelopes for the selected categorical and physical
segment execution, including all exhaustion and suffix-recursion branches. -/
namespace Blotto.BinarySegmentTraceSparsity
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization
open BinaryCategoricalPreparation BinaryCategoricalRun
open BinaryMeasuredTraceSparsity
open BinaryPRGHeapPrimitiveLifetime (cells)
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem sum_bound {α : Type*} (items : List (α × SignedWord)) :
    Bounded (BinaryQuadraticCategoricalMeasured.sum items).1.2 := by
  induction items with
  | nil => simp [BinaryQuadraticCategoricalMeasured.sum_nil,BinaryQuadraticCategoricalMeasured.sum_cons,Bounded,cells,listCells,arraySlots]
  | cons item rest ih =>
      rw [BinaryQuadraticCategoricalMeasured.sum_cons]
      exact prefix_two _ _ _ 1 1 (by simp [cells,listCells,arraySlots])
        ih ((by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _))

theorem prepare_bound {α : Type*} (fallback : α) (weights : WeightList α) :
    Bounded (BinaryQuadraticCategoricalMeasured.prepare fallback weights).1.2 := by
  rw [BinaryQuadraticCategoricalMeasured.prepare_record]
  split
  · simp [Bounded,cells,listCells,arraySlots]
  · simp [Bounded,cells,listCells,arraySlots]
  · dsimp only
    split
    · exact prefix_three _ _ _ _ 2 2 2 (by simp [cells,listCells,arraySlots])
        (sum_bound _) (BinaryArithmeticTraceSparsity.comparison_bound _ _)
        ((by simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous]; exact BinaryArithmeticTraceSparsity.measured_opcode_bound _ _ _))
    · exact prefix_two _ _ _ 2 2 (by simp [cells,listCells,arraySlots])
        (sum_bound _) (BinaryArithmeticTraceSparsity.comparison_bound _ _)

theorem categorical_bound {α : Type*} (store : BinarySeedLookupTree.Store) (fallback : α) (weights : WeightList α)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryWordCategoricalMeasured.run store fallback weights pc hp).1.2 := by
  rw [BinaryWordCategoricalMeasured.run_record]
  dsimp only
  cases hs : (BinaryQuadraticCategoricalMeasured.prepare fallback weights).1.1 with
  | done selected =>
      apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simpa only [List.forall_mem_cons,children_nil,and_true] using prepare_bound fallback weights
  | ask choice =>
      dsimp only
      cases hc : (BinaryWordCoinMeasured.sample store choice.probability pc hp).1.1.1 with
      | none =>
          apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
          simp only [List.forall_mem_cons,children_nil,and_true]
          exact ⟨prepare_bound _ _,BinaryCoinTraceSparsity.sample_bound _ _ _ _⟩
      | some bit =>
          cases bit
          · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
            simp only [List.forall_mem_cons,children_nil,and_true]
            exact ⟨prepare_bound _ _,BinaryCoinTraceSparsity.sample_bound _ _ _ _,
              categorical_bound store fallback choice.rest _ _⟩
          · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
            simp only [List.forall_mem_cons,children_nil,and_true]
            exact ⟨prepare_bound _ _,BinaryCoinTraceSparsity.sample_bound _ _ _ _⟩
termination_by weights.items.length
decreasing_by
  have hw := BinaryQuadraticCategoricalMeasured.prepared_choice_weights fallback weights choice hs
  have hl := rest_length choice
  rw [hw] at hl
  omega

theorem select_bound {n k : ℕ} (store : BinarySeedLookupTree.Store)
    (prepared : BinaryStoredSegmentProgram.Prepared n k) (fallback : Fin k)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryWordSegmentMeasured.select store prepared fallback pc hp).1.2 := by
  rw [BinaryWordSegmentMeasured.select_record]
  apply wrapList_bound k (8*k+16) (k+4) _
    (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simpa only [List.forall_mem_cons,children_nil,and_true] using categorical_bound store fallback _ pc hp

theorem segment_bound {n k : ℕ} (store : BinarySeedLookupTree.Store)
    (prepared : BinaryStoredSegmentProgram.Prepared n k) (fallback : Fin k)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryWordSegmentMeasured.run store prepared fallback K scalar pc hp).1.2 := by
  rw [BinaryWordSegmentMeasured.run_record]
  dsimp only
  split
  · apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using select_bound store prepared fallback pc hp
  · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨select_bound _ _ _ _ _,BinaryPointTraceSparsity.point_bound _ _ _ _⟩

end Blotto.BinarySegmentTraceSparsity
