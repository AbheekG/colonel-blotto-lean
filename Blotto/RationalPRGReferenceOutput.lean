import Blotto.StoredArrayReferenceList
import Blotto.RationalPRGStoredOutput

/-! A concrete reference-extraction loop is joined to the balanced native
serializer and both actual stored PRG producers. The source price includes
array extraction, under the declared address/control-word profile. -/

namespace Blotto.ReferenceStoredRowFrame

def frame {n : ℕ} (header : List Bool) (row : RationalResourceArray n) : List Bool :=
  BinaryNativeRowEncoder.frame header (StoredArrayReferenceList.list row.data)

theorem frame_data {n : ℕ} (header : List Bool) (row : RationalResourceArray n) :
    frame header row = BinaryNativeRowEncoder.stored header row := by
  simp only [frame, StoredArrayReferenceList.list_data, BinaryNativeRowEncoder.stored]

def work {n : ℕ} (primitive : ℕ → ℕ) (header : List Bool) (row : RationalResourceArray n) (W : ℕ) : ℕ :=
  StoredArrayReferenceList.work primitive (StoredArrayReferenceList.poolAddressWidth n W) n+
    BinaryNativeRowEncoder.frameWork primitive header (StoredArrayReferenceList.list row.data)

def bound (header : List Bool) (c n W : ℕ) : ℕ :=
  (5*c+6)*(n+1)*(StoredArrayReferenceList.poolAddressWidth n W+1)+
    3*header.length+n*(1024*(c+1)*(W+1)*(binaryWordWidth (W+2)+1)+3)+4

theorem work_bound {n : ℕ} (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (header : List Bool) (row : RationalResourceArray n) (W : ℕ)
    (hWidth : ∀ j, rationalWordWidth (row.allocation j) ≤ W) :
    work primitive header row W ≤ bound header c n W := by
  have hr := StoredArrayReferenceList.pool_work_bound primitive c hPrimitive n W
  have hf := BinaryNativeRowEncoder.stored_work_bound primitive c hPrimitive header row W hWidth
  unfold work bound
  rw [StoredArrayReferenceList.list_data]
  omega

theorem every_extraction_prefix {n : ℕ} (row : RationalResourceArray n)
    (used addressWidth payloadBits : ℕ) :
    payloadBits+addressWidth*(n+2*(StoredArrayReferenceList.advance row.data used
      ⟨n,by rw [row.size],[]⟩).tail.length) ≤ payloadBits+addressWidth*(3*n) := by
  simpa only [row.size, List.length_nil, Nat.mul_zero, Nat.add_zero] using
    StoredArrayReferenceList.every_prefix_payload_and_references row.data used addressWidth payloadBits
      ⟨n,by rw [row.size],[]⟩

end Blotto.ReferenceStoredRowFrame

namespace Blotto.RationalPRGOriginalInput

def referenceRichOutput {n : ℕ} (header : List Bool) (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : List Bool :=
  ReferenceStoredRowFrame.frame header (i.storedRichSample K bits)

def referencePoorOutput {n : ℕ} (header : List Bool) (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : List Bool :=
  ReferenceStoredRowFrame.frame header (i.storedPoorSample K bits)

theorem referenceRichOutput_data {n : ℕ} (header : List Bool) (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    referenceRichOutput header i K bits = storedRichOutput header i K bits :=
  ReferenceStoredRowFrame.frame_data header _

theorem referencePoorOutput_data {n : ℕ} (header : List Bool) (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    referencePoorOutput header i K bits = storedPoorOutput header i K bits :=
  ReferenceStoredRowFrame.frame_data header _

theorem referenceOutput_read {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (suffix : List Bool) :
    BinaryRatListFrame.readRow (referenceRichOutput (BinaryNatFrame.encode n) i K bits++suffix) =
      some (n,List.ofFn (i.richSample K bits),suffix) ∧
    BinaryRatListFrame.readRow (referencePoorOutput (BinaryNatFrame.encode n) i K bits++suffix) =
      some (n,List.ofFn (i.poorSample K bits),suffix) := by
  rw [referenceRichOutput_data,referencePoorOutput_data]
  exact ⟨i.storedRichOutput_read K bits suffix,i.storedPoorOutput_read K bits suffix⟩

theorem referenceOutput_work {n : ℕ} (header : List Bool) (i : RationalPRGOriginalInput n)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    ReferenceStoredRowFrame.work primitive header (i.storedRichSample K bits)
      (2^77*(i.originalInputWordWidth+K+6)) ≤
        ReferenceStoredRowFrame.bound header c n (2^77*(i.originalInputWordWidth+K+6)) ∧
    ReferenceStoredRowFrame.work primitive header (i.storedPoorSample K bits)
      (2^77*(i.originalInputWordWidth+K+6)) ≤
        ReferenceStoredRowFrame.bound header c n (2^77*(i.originalInputWordWidth+K+6)) :=
  ⟨ReferenceStoredRowFrame.work_bound primitive c hPrimitive header _ _ (fun j => (i.storedSample_widths K bits j).1),
    ReferenceStoredRowFrame.work_bound primitive c hPrimitive header _ _ (fun j => (i.storedSample_widths K bits j).2)⟩

end Blotto.RationalPRGOriginalInput
