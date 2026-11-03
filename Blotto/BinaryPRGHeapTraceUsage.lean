import Blotto.BinaryPRGHeapWriteLifetime

/-! Conservative composition of retained trace cells and source activations.
The borrowed caller region stays separate; no reclamation is assumed. -/

namespace Blotto.BinaryPRGHeapTraceUsage
open BinarySeedPreparationSpace BinaryRationalNormalization
open BinaryPRGHeapPrimitiveLifetime (cells)
open BinaryPRGHeapPackedStore (Packed)

def usage (trace : Trace) : ℕ := cells trace + framePeak trace

theorem usage_append (a b : Trace) : usage (a ++ b) ≤ usage a + usage b := by
  simp only [usage,BinaryPRGHeapPrimitiveLifetime.cells_append,framePeak_append]
  omega

theorem usage_under (depth : ℕ) (trace : Trace) : usage (under depth trace) ≤ usage trace + depth := by
  have h := framePeak_under depth trace
  simp only [usage,BinaryPRGHeapPrimitiveLifetime.cells_under]
  omega

def combine : List Trace → Trace
  | [] => []
  | child :: rest => under 2 child ++ combine rest

theorem combine_usage (children : List Trace) :
    usage (combine children) ≤ (children.map (fun trace => usage trace + 2)).sum := by
  induction children with
  | nil => simp [combine,usage,cells,listCells,arraySlots,framePeak]
  | cons child rest ih =>
      have hA := usage_append (under 2 child) (combine rest)
      have hU := usage_under 2 child
      simp only [combine,List.map_cons,List.sum_cons]
      omega

def wrap (slots frames : ℕ) (children : List Trace) : Trace :=
  [.frames frames,.arrayAllocation slots] ++ combine children

theorem wrap_usage (slots frames : ℕ) (children : List Trace) :
    usage (wrap slots frames children) ≤ slots + frames +
      (children.map (fun trace => usage trace + 2)).sum := by
  have hA := usage_append [.frames frames,.arrayAllocation slots] (combine children)
  have hC := combine_usage children
  have hHeader : usage [.frames frames,.arrayAllocation slots] = slots + frames := by
    simp [usage,cells,listCells,arraySlots,framePeak]
  rw [hHeader] at hA
  change usage (wrap slots frames children) ≤ _
  unfold wrap
  omega

def wrapList (list slots frames : ℕ) (children : List Trace) : Trace :=
  [.listAllocation list] ++ wrap slots frames children

theorem wrapList_usage (list slots frames : ℕ) (children : List Trace) :
    usage (wrapList list slots frames children) ≤ list + slots + frames +
      (children.map (fun trace => usage trace + 2)).sum := by
  have hA := usage_append [.listAllocation list] (wrap slots frames children)
  have hW := wrap_usage slots frames children
  have he : usage [.listAllocation list] = list := by simp [usage,cells,listCells,arraySlots,framePeak]
  rw [he] at hA
  unfold wrapList
  omega

theorem all_prefix (trace : Trace) (B : ℕ) (h : usage trace ≤ B) (borrowed steps : ℕ) :
    retainedHeap borrowed trace steps ≤ borrowed + B ∧
      framePeak (trace.take steps) ≤ B := by
  have hCells : listCells trace + arraySlots trace ≤ B := by unfold usage cells at h; omega
  have hFrame : framePeak trace ≤ B := by unfold usage at h; omega
  exact ⟨BinaryBooleanPrimitiveLifetime.prefix_heap trace B borrowed steps hCells,
    (framePeak_take_le _ _).trans hFrame⟩

def readEnvelope (H depth : ℕ) : ℕ :=
  16 * (BinaryPRGHeapStoredTree.readBound H depth +
    BinaryPRGWordStoreHeapMachine.lookupAllocation H depth + 2 * depth) +
      BinaryPRGHeapStoredTree.readBound H depth + 3 * depth + 44

theorem readEnvelope_mono {K H : ℕ} (h : K ≤ H) (depth : ℕ) :
    readEnvelope K depth ≤ readEnvelope H depth := by
  have hLog := binaryWordWidth_mono h
  unfold readEnvelope BinaryPRGHeapStoredTree.readBound BinaryPRGWordStoreHeapMachine.lookupAllocation
    BinaryPRGWordStoreHeapMachine.lookupBound BinaryPRGWordStoreHeapMachine.readBound
    BinaryPRGWordStoreHeapMachine.skipBound
  gcongr

theorem read_usage {depth : ℕ} (data : Packed depth) (address : FixedBinaryWord depth)
    (H : ℕ) (hH : data.heap.tape.length ≤ H) :
    usage (BinaryPRGHeapPackedLifetime.readWithTrace data address).2 ≤ readEnvelope H depth := by
  have hTrace := BinaryPRGHeapPackedLifetime.readWithTrace_bound data address
  obtain ⟨tree,hTree⟩ := data.realized
  have hCharge := BinaryPRGHeapStoredTree.readWithWork_bounds
    (⟨data.ruler,data.size,data.heap,data.root,data.valid,hTree⟩ : BinaryPRGHeapStoredTree.Stored tree) address
  dsimp only at hCharge
  rw [Packed.readWithWork_stored data hTree] at hTrace
  have h : usage (BinaryPRGHeapPackedLifetime.readWithTrace data address).2 ≤
      readEnvelope data.heap.tape.length depth := by
    unfold usage readEnvelope BinaryPRGHeapPrimitiveLifetime.price at *
    omega
  exact h.trans (readEnvelope_mono hH depth)

end Blotto.BinaryPRGHeapTraceUsage
