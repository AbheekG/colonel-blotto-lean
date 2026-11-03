import Blotto.BinaryReflectedTraceSparsity
import Blotto.BinaryGroupTraceSparsity

/-! The complete measured terminal dispatch has an unconditional structural
event certificate, including all four-word and reflected branches. -/
namespace Blotto.BinaryTerminalTraceSparsity
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization
open BinaryGroupInputs BinaryGroupSamplers
open BinaryMeasuredTraceSparsity
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem after_root_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (root : BinaryFourSmallMeasured.Root store) (hNext : root.1.1.2.value ≤ store.cap.value) (hRoot : Bounded root.1.2) :
    Bounded (BinaryFourSmallMeasured.afterRoot store input hC hAd K outer scalar root hNext).1.2 := by
  simp only [BinaryFourSmallMeasured.afterRoot_record]
  split
  · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using hRoot
  · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨hRoot,BinaryFourFactoryTraceSparsity.small_uniform_draw_bound _ _ _ _ _ _ _ _⟩
  · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨hRoot,BinaryReflectedTraceSparsity.reflected_bound _ _ _ _ _ _ _ _ _⟩

theorem small_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinarySmallRootSample.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryFourSmallMeasured.run store input hC hAd K outer scalar pc hp).1.2 :=
  after_root_bound _ _ _ _ _ _ _ _ _ (BinaryFourFactoryTraceSparsity.small_coin_bound _ _ _ _)

theorem ordered_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourParameters.Input) (hC : input.Canonical)
    (hAd : BinaryFourAdmissibility.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryFourOrderedMeasured.run store input hC hAd K outer scalar pc hp).1.2 := by
  simp only [BinaryFourOrderedMeasured.run_record]
  split
  · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨BinaryFourFactoryTraceSparsity.guard_bound _,BinaryFourFactoryTraceSparsity.gluing_draw_bound _ _ _ _ _ _ _ _⟩
  · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨BinaryFourFactoryTraceSparsity.guard_bound _,small_bound _ _ _ _ _ _ _ _ _⟩

theorem restored_bound (store : BinarySeedLookupTree.Store) (input : BinaryFourSpecSampler.Input) (hC : input.Canonical)
    (hAd : BinaryFourSpecSampler.Admissible input) (K : ℕ) (outer scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryFourRestoredMeasured.run store input hC hAd K outer scalar pc hp).1.2 := by
  simp only [BinaryFourRestoredMeasured.run_record,BinaryFourRestoredMeasured.afterOrder_record,BinaryFourRestoredMeasured.restore]
  split
  · apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨BinaryFourFactoryTraceSparsity.order_bound _,ordered_bound _ _ _ _ _ _ _ _ _⟩
  · apply wrap_bound 40 3 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨BinaryFourFactoryTraceSparsity.order_bound _,ordered_bound _ _ _ _ _ _ _ _ _,BinaryFactoryTraceSparsity.references_bound _ _⟩

theorem mixed_three_bound {n : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput 3) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (routes : FixedArrayTable n (BinaryGroupRoutes.Route 3)) (pivot : Fin n)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryWordGroupCompleteMeasured.mixedThreeRun store input hC hAd routes pivot K outer scalar pc hp).1.2 :=
  BinaryGroupTraceSparsity.after_mixed_bound _ _ _ _ (restored_bound _ _ _ _ _ _ _ _ _)

theorem draw_two_bound {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hTwo : m = 2) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryWordTerminalCompleteMeasured.drawTwo store input hC hAd hTwo routes pivot K scalar pc hp).1.2 := by
  subst m
  exact BinaryGroupTraceSparsity.mixed_two_complete_bound _ _ _ _ _ _ _ _ _ _

theorem draw_three_bound {n m : ℕ} (store : BinarySeedLookupTree.Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hThree : m = 3) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (pivot : Fin n) (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryWordTerminalCompleteMeasured.drawThree store input hC hAd hThree routes pivot K outer scalar pc hp).1.2 := by
  subst m
  exact mixed_three_bound store input hC hAd routes pivot K outer scalar pc hp

theorem terminal_bound {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : BinaryCachedTerminalPreparation.Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryWordTerminalCompleteMeasured.run store prepared hC hAd K outer scalar pc hp).1.2 := by
  simp only [BinaryWordTerminalCompleteMeasured.run_record]
  split
  · exact BinaryGroupTraceSparsity.branch_bound _ (BinaryGroupTraceSparsity.uniform_complete_bound _ _ _ _ _ _ _ _ _ _)
  · rename_i selected hPivot
    split
    · rename_i hTwo
      exact BinaryGroupTraceSparsity.branch_bound _ (draw_two_bound store prepared.mixed
        (prepared.mixed_canonical hC selected hPivot)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
        hTwo prepared.routes selected K scalar pc hp)
    · rename_i hTwo
      exact BinaryGroupTraceSparsity.branch_bound _ (draw_three_bound store prepared.mixed
        (prepared.mixed_canonical hC selected hPivot)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hPivot)
        ((prepared.count_bound hC hAd).resolve_left hTwo) prepared.routes selected K outer scalar pc hp)

theorem terminal_length_usage {n : ℕ} (store : BinarySeedLookupTree.Store) {input : BinaryTerminalGrouping.Input n}
    (prepared : BinaryCachedTerminalPreparation.Prepared input) (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryWordTerminalCompleteMeasured.run store prepared hC hAd K outer scalar pc hp).1.2.length ≤
      3*usage (BinaryWordTerminalCompleteMeasured.run store prepared hC hAd K outer scalar pc hp).1.2+3 :=
  length_usage _ (terminal_bound _ _ _ _ _ _ _ _ _)

end Blotto.BinaryTerminalTraceSparsity
