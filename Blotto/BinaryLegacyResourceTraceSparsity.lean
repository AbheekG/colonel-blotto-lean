import Blotto.BinaryCoinTraceSparsity
import Blotto.BinaryPRGHeapNativeLifetime

/-! Event certificates for the complete resource execution actually selected by
reflected setup. These concern its full legacy trace, not a data-only erasure. -/
namespace Blotto.BinaryLegacyResourceTraceSparsity
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization BinaryRationalEncoding
open BinaryMeasuredTraceSparsity
open BinaryPRGHeapPrimitiveLifetime (cells)
open BinaryResourceTraceLength (under_length)
open BinaryPRGWordControllerWordStore (Store Tree lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem prefix_five (header a b c d e : Trace) (p q r s t : ℕ)
    (hHeader : header.length+12 ≤ 3*cells header)
    (ha : Bounded a) (hb : Bounded b) (hc : Bounded c) (hd : Bounded d) (he : Bounded e) :
    Bounded (header++under p a++under q b++under r c++under s d++under t e) := by
  unfold Bounded at *
  simp only [List.length_append,under_length,BinaryPRGHeapPrimitiveLifetime.cells_append,
    BinaryPRGHeapPrimitiveLifetime.cells_under]
  omega

theorem register_build_bound (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) :
    Bounded (BinaryQuadraticResourcePairLifetime.buildWithTrace fallback ruler items).2 := by
  induction ruler generalizing items with
  | nil => cases items <;> simp [BinaryQuadraticResourcePairLifetime.buildWithTrace,Bounded,cells,listCells,arraySlots]
  | cons marker ruler ih => exact prefix_two _ _ _ 1 1 (by simp [cells,listCells,arraySlots]) (ih _) (ih _)

theorem register_scan_bound {height : ℕ} (tree : Tree height) (address : List Bool) :
    Bounded (BinaryQuadraticResourcePairLifetime.scanTreeWithTrace tree address).2 := by
  induction tree generalizing address with
  | leaf word => simp [BinaryQuadraticResourcePairLifetime.scanTreeWithTrace,Bounded,cells,listCells,arraySlots]
  | branch left right hl hr =>
      cases address with
      | nil => exact prefix_one _ _ 1 (by simp [cells,listCells,arraySlots]) (hl [])
      | cons bit rest =>
          cases bit
          · exact prefix_one _ _ 1 (by simp [cells,listCells,arraySlots]) (hl rest)
          · exact prefix_one _ _ 1 (by simp [cells,listCells,arraySlots]) (hr rest)

theorem register_lookup_bound {height : ℕ} (tree : Tree height) (address : FixedBinaryWord height) :
    Bounded (BinaryQuadraticResourcePairLifetime.lookupWithTrace tree address).2 :=
  prefix_two _ _ _ 2 2 (by simp [cells,listCells,arraySlots])
    (of_sparse _ (BinaryInitialTraceSparsity.reverse_sparse _ _)) (register_scan_bound _ _)

theorem register_write_scan_bound {height : ℕ} (tree : Tree height) (address : List Bool) (word : SignedWord) :
    Bounded (BinaryQuadraticResourcePairLifetime.writeScanWithTrace tree address word).2 := by
  induction tree generalizing address with
  | leaf old => simp [BinaryQuadraticResourcePairLifetime.writeScanWithTrace,Bounded,cells,listCells,arraySlots]
  | branch left right hl hr =>
      cases address with
      | nil => exact prefix_one _ _ 1 (by simp [cells,listCells,arraySlots]) (hl [])
      | cons bit rest =>
          cases bit
          · exact prefix_one _ _ 1 (by simp [cells,listCells,arraySlots]) (hl rest)
          · exact prefix_one _ _ 1 (by simp [cells,listCells,arraySlots]) (hr rest)

theorem register_write_bound {height : ℕ} (tree : Tree height) (address : FixedBinaryWord height) (word : SignedWord) :
    Bounded (BinaryQuadraticResourcePairLifetime.writeWithTrace tree address word).2 :=
  prefix_two _ _ _ 2 2 (by simp [cells,listCells,arraySlots])
    (of_sparse _ (BinaryInitialTraceSparsity.reverse_sparse _ _)) (register_write_scan_bound _ _ _)

theorem register_execute_bound (instruction : BinaryPRGWordControllerPairRegisters.Instruction)
    (registers : BinaryPRGWordControllerPairRegisters.Registers) :
    Bounded (BinaryQuadraticResourcePairLifetime.executeWithTrace instruction registers).2 :=
  prefix_five _ _ _ _ _ _ 2 2 2 2 2 (by simp [cells,listCells,arraySlots])
    (register_lookup_bound _ _) (register_lookup_bound _ _) (BinaryArithmeticTraceSparsity.opcode_bound _ _ _)
    (register_write_bound _ _ _) (of_sparse _ (BinaryInitialTraceSparsity.increment_sparse _))

theorem register_run_bound (program : List BinaryPRGWordControllerPairRegisters.Instruction)
    (registers : BinaryPRGWordControllerPairRegisters.Registers) :
    Bounded (BinaryQuadraticResourcePairLifetime.runWithTrace program registers).2 := by
  induction program generalizing registers with
  | nil => simp [BinaryQuadraticResourcePairLifetime.runWithTrace,Bounded,cells,listCells,arraySlots]
  | cons instruction rest ih =>
      exact prefix_two _ _ _ 2 1 (by simp [cells,listCells,arraySlots])
        (register_execute_bound _ _) (ih _)

theorem register_initial_bound (source : BinaryRationalPairProgram.Source) :
    Bounded (BinaryQuadraticResourcePairLifetime.initialWithTrace source).2 :=
  prefix_one _ _ 2 (by simp [cells,listCells,arraySlots]) (register_build_bound _ _ _)

theorem register_pair_bound (source : BinaryRationalPairProgram.Source) :
    Bounded (BinaryQuadraticResourcePairLifetime.preparedPairWithTrace source).2 :=
  prefix_two _ _ _ 2 2 (by simp [cells,listCells,arraySlots]) (register_initial_bound _) (register_run_bound _ _)

theorem register_outputs_bound (source : BinaryRationalPairProgram.Source) :
    Bounded (BinaryQuadraticResourcePairLifetime.outputsWithTrace source).2 :=
  prefix_four _ _ _ _ _ 2 2 2 2 (by simp [cells,listCells,arraySlots])
    (register_pair_bound _) (register_lookup_bound _ _) (register_lookup_bound _ _) (register_lookup_bound _ _)

theorem patch_bound (heap : BinaryPRGWordStoreHeap.Heap) (pointer ruler address : List Bool) (word : SignedWord) :
    Bounded (BinaryPRGHeapAccessLifetime.patchWithTrace heap pointer ruler address word).2 := by
  induction ruler generalizing heap pointer address with
  | nil =>
      unfold BinaryPRGHeapAccessLifetime.patchWithTrace
      dsimp only
      split
      · exact prefix_two _ _ _ 1 1 (by simp [cells,listCells,arraySlots])
          (of_sparse _ (BinaryInitialTraceSparsity.read_sparse _ _)) (of_sparse _ (BinaryInitialTraceSparsity.allocate_sparse _ _))
      · exact prefix_one _ _ 1 (by simp [cells,listCells,arraySlots]) (of_sparse _ (BinaryInitialTraceSparsity.read_sparse _ _))
  | cons marker ruler ih =>
      unfold BinaryPRGHeapAccessLifetime.patchWithTrace
      dsimp only
      split
      · rename_i left right hFound
        have hChanged : Bounded (if address.headD false then
            BinaryPRGHeapAccessLifetime.patchWithTrace heap right ruler address.tail word
          else BinaryPRGHeapAccessLifetime.patchWithTrace heap left ruler address.tail word).2 := by
          split <;> exact ih _ _ _
        split
        · exact prefix_two _ _ _ 1 1 (by simp [cells,listCells,arraySlots])
            (of_sparse _ (BinaryInitialTraceSparsity.read_sparse _ _)) hChanged
        · exact prefix_three _ _ _ _ 1 1 1 (by simp [cells,listCells,arraySlots])
            (of_sparse _ (BinaryInitialTraceSparsity.read_sparse _ _)) hChanged
            (of_sparse _ (BinaryInitialTraceSparsity.allocate_sparse _ _))
      · exact prefix_one _ _ 1 (by simp [cells,listCells,arraySlots]) (of_sparse _ (BinaryInitialTraceSparsity.read_sparse _ _))

theorem packed_read_bound {depth : ℕ} (data : BinaryPRGHeapPackedStore.Packed depth)
    (address : FixedBinaryWord depth) : Bounded (BinaryPRGHeapPackedLifetime.readWithTrace data address).2 := by
  have h := BinaryInitialTraceSparsity.packed_read_sparse data address
  rw [BinaryHeapPackedReadMeasured.read_erases] at h
  exact of_sparse _ h

theorem enumeration_bound {w : ℕ} (cap : FixedBinaryWord w) :
    Bounded (BinaryPRGHeapEnumerationLifetime.allFromBitsWithTrace cap).2 := by
  have h := BinaryInitialTraceSparsity.allFromBits_sparse cap
  rw [BinaryHeapEnumerationWidthMeasured.allFromBits_erases] at h
  exact of_sparse _ h

theorem packed_write_bound {depth : ℕ} (data : BinaryPRGHeapPackedStore.Packed depth)
    (address : FixedBinaryWord depth) (word : SignedWord) :
    Bounded (BinaryPRGHeapPackedLifetime.writeWithTrace data address word).2 :=
  prefix_two _ _ _ 1 1 (by simp [cells,listCells,arraySlots])
    (of_sparse _ (BinaryInitialTraceSparsity.reverse_sparse _ _)) (patch_bound _ _ _ _ _)

theorem writes_bound {depth : ℕ} (data : BinaryPRGHeapPackedStore.Packed depth)
    (changes : List (BinaryPRGHeapWriteSequence.Change depth)) :
    Bounded (BinaryPRGHeapWriteLifetime.executeWithTrace data changes).2 := by
  induction changes generalizing data with
  | nil => simp [BinaryPRGHeapWriteLifetime.executeWithTrace,Bounded,cells,listCells,arraySlots]
  | cons item rest ih =>
      exact prefix_two _ _ _ 1 1 (by simp [cells,listCells,arraySlots])
        (packed_write_bound _ _ _) (ih _)

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}

theorem scan_bound (limits : Stored capacity.tree) (bids : BinaryPRGHeapPackedStore.Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    Bounded (BinaryPRGHeapScanLifetime.scanWithTrace limits bids addresses).2 := by
  have h := BinaryInitialTraceSparsity.heap_scan_sparse limits bids addresses
  rw [BinaryHeapScanMeasured.scan_trace] at h
  exact of_sparse _ h

theorem pair_source_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    Bounded (BinaryPRGHeapPairLifetime.sourceWithTrace (hC := hC) limits state first second tail he).2 := by
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨packed_read_bound _ _,packed_read_bound _ _,
    packed_read_bound _ _,packed_read_bound _ _⟩

theorem pair_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    Bounded (BinaryPRGHeapPairLifetime.pairWithTrace (hC := hC) limits state first second tail he).2 := by
  apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨pair_source_bound _ _ _ _ _ _,register_outputs_bound _⟩

theorem update_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap)) (chosen : SignedWord) :
    Bounded (BinaryPRGHeapUpdateLifetime.updateWithTrace limits state first second tail chosen).2 := by
  apply wrapList_bound _ 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨packed_read_bound _ _,packed_read_bound _ _,
    BinaryArithmeticTraceSparsity.opcode_bound _ _ _,BinaryArithmeticTraceSparsity.opcode_bound _ _ _,writes_bound _ _,
    scan_bound _ _ _⟩

theorem select_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs) (branch : Bool) :
    Bounded (BinaryPRGHeapLoopLifetime.selectWithTrace limits state first second tail he outputs hOutputs branch).2 := by
  apply wrap_bound 16 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simpa only [List.forall_mem_cons,children_nil,and_true] using update_bound limits state first second tail _

theorem loop_bound (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    Bounded (BinaryPRGHeapLoopLifetime.runWithTrace seed limits hC state pc hp).2 := by
  unfold BinaryPRGHeapLoopLifetime.runWithTrace
  split
  · rename_i first second tail he
    dsimp only
    split
    · apply wrap_bound 24 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simp only [List.forall_mem_cons,children_nil,and_true]
      constructor
      · exact pair_bound _ _ _ _ _ _
      · have h := BinaryCoinTraceSparsity.sample_bound seed
          (BinaryPRGHeapPairLifetime.pairWithTrace (hC := hC) limits state first second tail he).1.probability pc hp
        rw [BinaryWordCoinMeasured.sample_erases] at h
        exact h
    · rename_i branch hBranch
      apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
      simp only [List.forall_mem_cons,children_nil,and_true]
      refine ⟨pair_bound _ _ _ _ _ _,?_,select_bound _ _ _ _ _ _ _ _ _,loop_bound _ _ _ _ _ _⟩
      have h := BinaryCoinTraceSparsity.sample_bound seed
        (BinaryPRGHeapPairLifetime.pairWithTrace (hC := hC) limits state first second tail he).1.probability pc hp
      rw [BinaryWordCoinMeasured.sample_erases] at h
      exact h
  · exact wrap_bound 16 2 [] (by simp) (by decide)
termination_by state.active.length
decreasing_by
  apply BinaryPRGHeapLoopLifetime.selectWithTrace_progress

theorem arrays_bound (capacity resource : FixedArrayTable n SignedWord) :
    Bounded (BinaryPRGHeapInitialLifetime.arraysWithTrace capacity resource).2 := by
  apply wrapList_bound (3*n) 64 (3*n+4) _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨of_sparse _ (BinaryInitialTraceSparsity.count_sparse _ _),
    of_sparse _ (BinaryInitialTraceSparsity.ruler_prepare_sparse _ _ _),of_sparse _ (BinaryInitialTraceSparsity.ruler_prepare_sparse _ _ _)⟩

theorem initial_bound (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j)) :
    Bounded (BinaryPRGHeapInitialLifetime.initialWithTrace capacity resource hC hR).2 := by
  unfold BinaryPRGHeapInitialLifetime.initialWithTrace
  dsimp only
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  refine ⟨arrays_bound _ _,enumeration_bound _,?_⟩
  rw [BinaryPRGHeapScanComparisonWork.scanWithFullWork_erases]
  exact scan_bound _ _ _

theorem source_bound (seed : BinarySeedLookupTree.Store) (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j)) (hR : ∀ j,CanonicalWord (resource.read j))
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    Bounded (BinaryPRGHeapNativeLifetime.sourceWithTraceAndWork seed capacity resource hC hR pc hp).1.2 := by
  apply wrap_bound 32 2 _ (hSlots := by simp only [List.length_cons,List.length_nil]; omega)
  simp only [List.forall_mem_cons,children_nil,and_true]
  exact ⟨initial_bound _ _ _ _,loop_bound _ _ _ _ _ _⟩

end Blotto.BinaryLegacyResourceTraceSparsity
