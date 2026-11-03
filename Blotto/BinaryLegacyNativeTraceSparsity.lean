import Blotto.BinaryLegacyResourceTraceSparsity

/-! The reflected resource interface includes actual address enumeration,
materialization and native wrapping after its complete resource loop. -/
namespace Blotto.BinaryLegacyNativeTraceSparsity
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization BinaryRationalEncoding
open BinaryMeasuredTraceSparsity BinaryLegacyResourceTraceSparsity
open BinaryPRGWordControllerWordStore (Store)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapResourceLoop (Finished)
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem collect_bound {w : ℕ} {cap : FixedBinaryWord w} (bids : BinaryPRGHeapPackedStore.Packed w)
    (ids : List (Address w cap)) : Bounded (BinaryPRGHeapMaterializationLifetime.collectWithTrace bids ids).2 := by
  induction ids with
  | nil => exact wrap_bound 8 1 [] (by simp) (by decide)
  | cons address rest ih =>
      apply wrapList_bound 1 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simp only [List.forall_mem_cons,children_nil,and_true]
      exact ⟨packed_read_bound _ _,ih⟩

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}

theorem row_words_bound (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) :
    Bounded (BinaryPRGHeapMaterializationLifetime.rowWordsWithTrace capWord hCap state).2 := by
  apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨enumeration_bound _,collect_bound _ _⟩

theorem row_table_bound (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) :
    Bounded (BinaryPRGHeapMaterializationLifetime.rowTableWithTrace capWord hCap state).2 := by
  apply wrap_bound (2*(n+1)^2+8) (n+4) _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simpa only [List.forall_mem_cons,children_nil,and_true] using row_words_bound capWord hCap state

theorem decode_bound (address : Address capacity.width capacity.cap) :
    Bounded (BinaryPRGHeapMaterializationLifetime.decodeWithTrace (hCount := hCount) address).2 :=
  wrap_bound 16 _ [] (by simp) (by decide)

theorem active_bound (ids : List (Address capacity.width capacity.cap)) :
    Bounded (BinaryPRGHeapMaterializationLifetime.activeWithTrace (hCount := hCount) ids).2 := by
  induction ids with
  | nil => exact wrap_bound 8 1 [] (by simp) (by decide)
  | cons address rest ih =>
      apply wrapList_bound 1 8 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simp only [List.forall_mem_cons,children_nil,and_true]
      exact ⟨decode_bound _,ih⟩

theorem state_bound (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap)
    (state : Finished capacity n hCount) :
    Bounded (BinaryPRGHeapMaterializationLifetime.stateWithTrace capWord hCap state).2 := by
  apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨row_table_bound _ _ _,active_bound _⟩

theorem materialize_bound (nativeCapacity : FixedArrayTable n SignedWord)
    (hTable : BinaryPRGWordControllerBooleanResourceUpdate.table capacity.cap capacity.tree n hCount = nativeCapacity)
    (capWord : FixedBinaryWord capacity.width) (hCap : capWord = capacity.cap) (state : Finished capacity n hCount) :
    Bounded (BinaryPRGHeapMaterializationLifetime.materializeWithTrace nativeCapacity hTable capWord hCap state).2 := by
  apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simpa only [List.forall_mem_cons,children_nil,and_true] using state_bound capWord hCap state

theorem native_bound (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    Bounded (BinaryPRGHeapNativeLifetime.nativeWithTraceAndWork seed capacity resource hC hR pc hp).1.2 := by
  unfold BinaryPRGHeapNativeLifetime.nativeWithTraceAndWork
  dsimp only
  split
  · apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simpa only [List.forall_mem_cons,children_nil,and_true] using source_bound seed capacity resource hC hR pc hp
  · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
    simp only [List.forall_mem_cons,children_nil,and_true]
    exact ⟨source_bound _ _ _ _ _ _ _,materialize_bound _ _ _ _ _⟩

end Blotto.BinaryLegacyNativeTraceSparsity
