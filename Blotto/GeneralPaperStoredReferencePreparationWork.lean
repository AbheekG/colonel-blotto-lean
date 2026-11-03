import Blotto.GeneralPaperStoredHeaderPreparationWork

/-! Price every actual reference-entry construction, index increment and
left-only append. Bounds use valid owners and their actual capacity, with
no payload precision or repeated indexed-list lookup. -/
namespace Blotto.GeneralPaperStoredReferencePreparationWork
open GeneralPaperReferenceRegionSlots GeneralPaperSequentialLayout
open GeneralPaperStoredHeaderPreparationWork (scalarBound)
open GeneralPaperReferenceSlotConstruction (Entry)
open GeneralPaperEncodedScalarStorage (natBits)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def batchElement (model : RationalCostModel) (S A : ℕ) : ℕ :=
  GeneralPaperStoredReferenceReadWork.slotBound model S A (A + 8) + scalarBound model S A + 128 * (S + A + 1)

def perElement (model : RationalCostModel) (S A : ℕ) : ℕ :=
  batchElement model S A + 3 * A + 1 + 64 * (S + A + 1)

theorem batch_work (model : RationalCostModel) (S A base fixed start : ℕ)
    (values : List (FixedBinaryWord A))
    (hBase : binaryWordWidth base ≤ A + 8) (hFixed : binaryWordWidth fixed ≤ A + 8)
    (hCount : binaryWordWidth (start + values.length) ≤ A + 8) :
    (GeneralPaperReferenceSlotBatch.run model S A base fixed 1 0 start values).work ≤
      values.length * batchElement model S A + 64 * (S + A + 1) := by
  induction values generalizing start with
  | nil => simp only [GeneralPaperReferenceSlotBatch.run,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons value values ih =>
    have hIndex := (binaryWordWidth_mono (Nat.le_add_right start (value :: values).length)).trans hCount
    have hA : binaryWordWidth A ≤ A + 8 := by have h := Nat.log2_le_self A; unfold binaryWordWidth; omega
    have hSlot := GeneralPaperStoredReferenceReadWork.slot_work model S A base fixed 1 start 0 (A + 8) value
      hA hBase hFixed (by change 1 ≤ A + 8; omega) hIndex (by change 1 ≤ A + 8; omega)
    have hInc := GeneralPaperStoredHeaderPreparationWork.increment_work model S A start hIndex
    have hEnd : start + 1 + values.length = start + (value :: values).length := by simp only [List.length_cons]; omega
    have hTail := ih (start + 1) (by rw [hEnd]; exact hCount)
    change _ + _ + (GeneralPaperReferenceSlotBatch.run model S A base fixed 1 0 (start + 1) values).work +
      128 * (S + A + 1) ≤ (values.length + 1) * batchElement model S A + 64 * (S + A + 1)
    unfold batchElement at hTail ⊢
    nlinarith only [hSlot,hInc,hTail]

theorem header_batch_work (model : RationalCostModel) (S A : ℕ) (header : Header A)
    (hA : 0 < A) (hValid : Valid header) (hCap : header.region.stop < 2 ^ A) :
    (batch model S A header).work ≤ header.targets.length * batchElement model S A + 64 * (S + A + 1) := by
  obtain ⟨hStart,_,hFixed,hCount⟩ := GeneralPaperStoredHeaderPreparationWork.owner_widths header hA hValid hCap
  exact batch_work model S A header.region.start header.fixed 0 header.targets (by omega) (by omega) (by simpa only [Nat.zero_add] using hCount.trans (show A ≤ A + 8 by omega))

theorem append_work (model : RationalCostModel) (S A : ℕ) (header : Header A)
    (tail : List (Entry A)) (hA : 0 < A) (hValid : Valid header) (hCap : header.region.stop < 2 ^ A) :
    (GeneralPaperReferenceRegionProgram.append S A (batch model S A header).entries tail).2 ≤
      header.targets.length * (3 * A + 1 + 64 * (S + A + 1)) + 64 * (S + A + 1) := by
  have hEach : ∀ entry ∈ (batch model S A header).entries,natBits entry.position ≤ A + 1 := by
    intro entry he
    obtain ⟨i,target,_,hi,rfl⟩ := GeneralPaperReferenceSlotBatch.member_index model S A header.region.start header.fixed 1 0 0 header.targets entry he
    have hFits := GeneralPaperReferenceSlotConstruction.fits model S A header.region.start header.fixed 1 header.targets.length i 0 target
      (by omega) (by decide) (capacity header hValid hCap)
    have hw := binaryWordWidth_le_of_lt_pow hA hFits
    unfold natBits
    omega
  have hSum : ((batch model S A header).entries.map (fun e => natBits e.position)).sum ≤
      (batch model S A header).entries.length * (A + 1) := by
    suffices h : ∀ entries : List (Entry A),(∀ e ∈ entries,natBits e.position ≤ A + 1) →
        (entries.map (fun e => natBits e.position)).sum ≤ entries.length * (A + 1) from h _ hEach
    intro entries
    induction entries with
    | nil => intro _; simp
    | cons entry entries ih =>
      intro hEach
      have hh := hEach entry (List.mem_cons_self ..)
      have ht := ih (fun e he => hEach e (List.mem_cons_of_mem _ he))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith only [hh,ht]
  have hLength : (batch model S A header).entries.length = header.targets.length :=
    GeneralPaperReferenceSlotBatch.count model S A header.region.start header.fixed 1 0 0 header.targets
  rw [GeneralPaperReferenceRegionProgram.append_work,hLength]
  rw [hLength] at hSum
  nlinarith only [hSum]

theorem collect_work (model : RationalCostModel) (S A : ℕ) (headers : List (Header A))
    (hA : 0 < A) (hValid : ∀ header ∈ headers,Valid header)
    (hCap : ∀ header ∈ headers,header.region.stop < 2 ^ A) :
    (GeneralPaperReferenceRegionProgram.collect model S A headers).work ≤
      GeneralPaperReferenceHeaderSlotArea.slots headers * perElement model S A +
        headers.length * (192 * (S + A + 1)) + 64 * (S + A + 1) := by
  induction headers with
  | nil => simp only [GeneralPaperReferenceRegionProgram.collect,GeneralPaperReferenceHeaderSlotArea.slots,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons header headers ih =>
    have hh : header ∈ header :: headers := List.mem_cons_self ..
    have hBatch := header_batch_work model S A header hA (hValid header hh) (hCap header hh)
    have hAppend := append_work model S A header (GeneralPaperReferenceRegionProgram.collect model S A headers).entries hA (hValid header hh) (hCap header hh)
    have ht := ih (fun h hm => hValid h (List.mem_cons_of_mem _ hm)) (fun h hm => hCap h (List.mem_cons_of_mem _ hm))
    change (batch model S A header).work + _ + _ + 64 * (S + A + 1) ≤ _
    simp only [GeneralPaperReferenceHeaderSlotArea.slots,List.map_cons,List.sum_cons,List.length_cons] at ht ⊢
    unfold perElement at *
    nlinarith only [hBatch,hAppend,ht]

end Blotto.GeneralPaperStoredReferencePreparationWork
