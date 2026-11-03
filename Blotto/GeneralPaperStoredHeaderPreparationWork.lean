import Blotto.GeneralPaperStoredFramedDrawWork

/-! Complete executed count-header preparation has a metadata-only price.
The bound is linear in the actual reserved prefix and target count. Owner
validity and capacity derive the counter and region widths internally. -/
namespace Blotto.GeneralPaperStoredHeaderPreparationWork
open GeneralPaperReferenceRegionSlots GeneralPaperSequentialLayout
open GeneralPaperEncodedScalarStorage (natBits)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def scalarBound (model : RationalCostModel) (S A : ℕ) : ℕ :=
  5 * model.rat (8 * (A + 9)) + 16 * S + 16

def encodeBound (model : RationalCostModel) (S A : ℕ) : ℕ :=
  A * GeneralPaperStoredWordEncoding.stepBound model S A (A + 8) + 64 * S + 64

def perElement (model : RationalCostModel) (S A : ℕ) : ℕ :=
  scalarBound model S A + 2 * encodeBound model S A + 1024 * (S + A + 1) + 16 * (A + 1)

theorem increment_work (model : RationalCostModel) (S A n : ℕ)
    (hn : binaryWordWidth n ≤ A + 8) :
    (GeneralPaperNaturalScalarStep.run model S .add n 1).2 ≤ scalarBound model S A := by
  have hAdd := GeneralPaperRayOperandWidthEnvelope.word_add n 1
  apply GeneralPaperNaturalScalarStep.work model S .add n 1 (8 * (A + 9))
  · unfold GeneralPaperNaturalScalarStep.word; omega
  · change 2 ≤ 8 * (A + 9); omega
  · change 1 + binaryWordWidth (n + 1) ≤ 8 * (A + 9)
    have hOne : binaryWordWidth 1 = 1 := by decide
    omega

theorem copy_price (model : RationalCostModel) (S A n : ℕ)
    (hn : binaryWordWidth n ≤ A + 8) :
    GeneralPaperHeaderTargetCopy.price model S A n ≤
      n * (scalarBound model S A + A + 128 * (S + A + 1)) + 64 * (S + A + 1) := by
  induction n with
  | zero => simp only [GeneralPaperHeaderTargetCopy.price,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ n ih =>
    have hWidth := (binaryWordWidth_mono (Nat.le_succ n)).trans hn
    have h := increment_work model S A n hWidth
    have ht := ih hWidth
    rw [GeneralPaperHeaderTargetCopy.price]
    nlinarith only [h,ht]

theorem owner_widths {A : ℕ} (header : Header A) (hA : 0 < A)
    (hValid : Valid header) (hCap : header.region.stop < 2 ^ A) :
    binaryWordWidth header.region.start ≤ A ∧ binaryWordWidth header.region.length ≤ A ∧
      binaryWordWidth header.fixed ≤ A ∧ binaryWordWidth header.targets.length ≤ A := by
  have hSlots : header.fixed + header.targets.length ≤ header.region.length := by
    have hm := Nat.mul_le_mul_right (header.fixed + header.targets.length) hA
    unfold Valid at hValid
    nlinarith only [hm,hValid]
  unfold Region.stop at hCap
  exact ⟨binaryWordWidth_le_of_lt_pow hA (by omega),
    binaryWordWidth_le_of_lt_pow hA (by omega),
    binaryWordWidth_le_of_lt_pow hA (by omega),
    binaryWordWidth_le_of_lt_pow hA (by omega)⟩

theorem run_work (model : RationalCostModel) (S A : ℕ) (header : Header A)
    (hA : 0 < A) (hValid : Valid header) (hCap : header.region.stop < 2 ^ A) :
    (GeneralPaperHeaderCountExpansion.run model S A header).2 ≤
      (header.fixed + header.targets.length + 1) * perElement model S A := by
  obtain ⟨hStart,hLength,hFixed,hCount⟩ := owner_widths header hA hValid hCap
  by_cases hf : header.fixed = 0
  · simp only [GeneralPaperHeaderCountExpansion.run,hf,ite_true]
    have hp : natBits 0 + 64 * (S + A + 1) ≤ perElement model S A := by
      unfold perElement natBits
      change (1 + 1) + 64 * (S + A + 1) ≤ _
      omega
    exact hp.trans (by simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right (perElement model S A) (show 1 ≤ 0 + header.targets.length + 1 by omega))
  · have hCopy := copy_price model S A header.targets.length (by omega)
    have hEncode := GeneralPaperStoredWordEncoding.work model S A header.targets.length (A + 8) (by omega)
    have hZero := GeneralPaperStoredWordEncoding.work model S A 0 (A + 8) (by change 1 ≤ A + 8; omega)
    have hRegion : GeneralPaperLastRegionSelection.price S A header.region ≤ 4 * A + 2 + 64 * (S + A + 1) := by
      unfold GeneralPaperLastRegionSelection.price natBits
      omega
    rw [GeneralPaperHeaderCountExpansion.work_positive model S A header hf]
    have hSub : (header.fixed - 1) * (A + 64 * (S + A + 1)) ≤ header.fixed * (A + 64 * (S + A + 1)) :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    change _ ≤ encodeBound model S A at hEncode hZero
    have hF := Nat.mul_le_mul_left header.fixed (show 2 * (A + 64 * (S + A + 1)) ≤ perElement model S A by unfold perElement; omega)
    have hN := Nat.mul_le_mul_left header.targets.length (show scalarBound model S A + A + 128 * (S + A + 1) ≤ perElement model S A by unfold perElement; omega)
    have hRest : 2 * encodeBound model S A + (4 * A + 2 + 64 * (S + A + 1)) + natBits header.fixed + 320 * (S + A + 1) ≤ perElement model S A := by
      unfold perElement natBits
      omega
    nlinarith only [hCopy,hEncode,hZero,hRegion,hSub,hF,hN,hRest]

theorem expanded_length {A : ℕ} (header : Header A) :
    (GeneralPaperHeaderCountExpansion.expanded header).targets.length = header.fixed + header.targets.length := by
  by_cases hf : header.fixed = 0
  · rw [GeneralPaperHeaderCountExpansion.zero_fixed header hf,hf,Nat.zero_add]
  · exact GeneralPaperHeaderCountExpansion.length header hf

theorem headers_work (model : RationalCostModel) (S A : ℕ) (headers : List (Header A))
    (hA : 0 < A) (hValid : ∀ header ∈ headers,Valid header)
    (hCap : ∀ header ∈ headers,header.region.stop < 2 ^ A) :
    (headers.map (fun header => (GeneralPaperHeaderCountExpansion.run model S A header).2)).sum ≤
      (GeneralPaperReferenceHeaderSlotArea.slots (headers.map GeneralPaperHeaderCountExpansion.expanded) + headers.length) * perElement model S A := by
  induction headers with
  | nil => simp only [List.map_nil,List.sum_nil,List.length_nil,GeneralPaperReferenceHeaderSlotArea.slots,Nat.zero_add,Nat.zero_mul,le_refl]
  | cons header headers ih =>
    have hh : header ∈ header :: headers := List.mem_cons_self ..
    have hHead := run_work model S A header hA (hValid header hh) (hCap header hh)
    have ht := ih (fun h hm => hValid h (List.mem_cons_of_mem _ hm)) (fun h hm => hCap h (List.mem_cons_of_mem _ hm))
    simp only [List.map_cons,List.sum_cons,List.length_cons,GeneralPaperReferenceHeaderSlotArea.slots,expanded_length] at ht ⊢
    nlinarith only [hHead,ht]

end Blotto.GeneralPaperStoredHeaderPreparationWork
