import Blotto.BinaryArithmeticTraceSparsity
import Blotto.BinaryCacheTraceSparsity
import Blotto.BinaryWordCoinMeasured

/-! Structural event bounds for the reached Boolean-PC coin, including EOF
and its recursive continuation. No numerical-width or outcome premise is used. -/
namespace Blotto.BinaryCoinTraceSparsity
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryRationalNormalization
open BinarySeedLookupTree (Store Tree)
open BinaryMeasuredTraceSparsity
open BinaryPRGHeapPrimitiveLifetime (cells)
open BinaryResourceTraceLength (under_length)
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem same_bound (first second : List Bool) : Bounded (BinaryWordCoinPrimitivesMeasured.same first second).1.2 := by
  induction first generalizing second with
  | nil => cases second <;> simp [BinaryWordCoinPrimitivesMeasured.same,Bounded,cells,listCells,arraySlots]
  | cons bit rest ih => cases second with
    | nil => simp [BinaryWordCoinPrimitivesMeasured.same,Bounded,cells,listCells,arraySlots]
    | cons other tail =>
        unfold BinaryWordCoinPrimitivesMeasured.same
        split
        · exact prefix_one _ _ 1 (by simp [cells,listCells,arraySlots]) (ih tail)
        · simp [Bounded,cells,listCells,arraySlots]

theorem scan_tree_bound {height : ℕ} (tree : Tree height) (address : List Bool) :
    Bounded (BinaryWordStoreLifetime.scanTreeWithTrace tree address).2 := by
  induction tree generalizing address with
  | leaf bit => simp [BinaryWordStoreLifetime.scanTreeWithTrace,Bounded,cells,listCells,arraySlots]
  | branch left right hl hr =>
      cases address with
      | nil => exact prefix_one _ _ 1 (by simp [cells,listCells,arraySlots]) (hl [])
      | cons bit rest =>
          cases bit
          · exact prefix_one _ _ 1 (by simp [cells,listCells,arraySlots]) (hl rest)
          · exact prefix_one _ _ 1 (by simp [cells,listCells,arraySlots]) (hr rest)

theorem lookup_bound (store : Store) (address : FixedBinaryWord store.width) :
    Bounded (BinaryWordCoinPrimitivesMeasured.lookup store address).1.2 := by
  rw [BinaryWordCoinPrimitivesMeasured.lookup_erases]
  exact prefix_two _ _ _ 2 2 (by simp [cells,listCells,arraySlots])
    (of_sparse _ (BinaryInitialTraceSparsity.reverse_sparse address.bits [])) (scan_tree_bound _ _)

theorem zero_bound (bits : List Bool) : Bounded (BinaryWordCoinPrimitivesMeasured.zero bits).1.2 := by
  rw [BinaryWordCoinPrimitivesMeasured.zero_erases]
  exact of_sparse _ (BinaryInitialTraceSparsity.scan_sparse bits)

theorem guard_bound {w : ℕ} (first second : FixedBinaryWord w) :
    Bounded (BinaryWordCoinPrimitivesMeasured.lt first second).1.2 := by
  rw [BinaryWordCoinPrimitivesMeasured.lt_erases]
  exact of_sparse _ (BinaryInitialTraceSparsity.guard_sparse first second)

theorem step_bound {w : ℕ} (a b : FixedBinaryWord w) :
    Bounded (BinaryWordCoinPrimitivesMeasured.step a b).1.2 := by
  rw [BinaryWordCoinPrimitivesMeasured.step_erases]
  simp only [Bounded,BinaryWordCoinLifetime.stepWithTrace,cells,listCells,arraySlots,List.length_cons,List.length_nil]
  omega

theorem increment_bound {w : ℕ} (word : FixedBinaryWord w) :
    Bounded (BinaryWordCoinPrimitivesMeasured.increment word).1.2 := by
  rw [BinaryWordCoinPrimitivesMeasured.increment_erases]
  exact of_sparse _ (BinaryInitialTraceSparsity.increment_sparse word)

theorem pad_bound (W : ℕ) (bits : List Bool) : Bounded (BinaryWordCoinPrimitivesMeasured.pad W bits).1.2 := by
  rw [BinaryWordCoinPrimitivesMeasured.pad_erases]
  exact prefix_two _ _ _ 2 2 (by simp [cells,listCells,arraySlots])
    (of_sparse _ (BinaryCacheTraceSparsity.replicate_sparse _ _))
    (of_sparse _ (BinaryArithmeticTraceSparsity.append_sparse _ _))

theorem run_bound {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Bounded (BinaryWordCoinMeasured.run store a b pc hp).1.2 := by
  have hz := zero_bound a.bits
  have he := same_bound a.bits b.bits
  have hg := guard_bound pc store.cap
  have hl := lookup_bound store pc
  have hs := step_bound a b
  have hi := increment_bound pc
  unfold BinaryWordCoinMeasured.run
  dsimp only
  split
  · exact prefix_one _ _ 2 (by simp [cells,listCells,arraySlots]) hz
  · split
    · exact prefix_two _ _ _ 2 2 (by simp [cells,listCells,arraySlots]) hz he
    · split
      · rename_i hRead
        split
        · have hLater := run_bound store (BinaryWordCoinPrimitivesMeasured.step a b).1.1.2 b
            (BinaryWordCoinPrimitivesMeasured.increment pc).1.1.1 (BinaryWordCoinMeasured.advance_bound store pc hRead)
          unfold Bounded at hz he hg hl hs hi hLater ⊢
          simp only [List.length_append,under_length,BinaryPRGHeapPrimitiveLifetime.cells_append,
            BinaryPRGHeapPrimitiveLifetime.cells_under,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,List.length_cons,List.length_nil] at *
          omega
        · unfold Bounded at hz he hg hl hs hi ⊢
          simp only [List.length_append,under_length,BinaryPRGHeapPrimitiveLifetime.cells_append,
            BinaryPRGHeapPrimitiveLifetime.cells_under,cells,listCells_append,arraySlots_append,listCells_under,arraySlots_under,listCells,arraySlots,List.length_cons,List.length_nil] at *
          omega
      · exact prefix_three _ _ _ _ 2 2 2 (by simp [cells,listCells,arraySlots]) hz he hg
termination_by store.cap.value-pc.value
decreasing_by
  have hRead' : (BinaryWordCoinPrimitivesMeasured.lt pc store.cap).1.1 = true := by assumption
  have hn := BinaryWordCoinMeasured.advance_value store pc hRead'
  have hr : pc.value < store.cap.value := (BinaryIndexWord.lt_value pc store.cap).mp
    (by simpa only [BinaryWordCoinPrimitivesMeasured.lt_erases,BinaryWordStoreLifetime.ltWithTrace_erases] using hRead')
  omega

theorem sample_bound (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) : Bounded (BinaryWordCoinMeasured.sample store word pc hp).1.2 := by
  exact prefix_three _ _ _ _ 2 2 2 (by simp [cells,listCells,arraySlots])
    (pad_bound _ _) (pad_bound _ _) (run_bound _ _ _ _ _)

end Blotto.BinaryCoinTraceSparsity
