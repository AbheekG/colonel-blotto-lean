import Blotto.GeneralPaperHeaderTargetCopy

/-! Positive-prefix headers initialize a count and zero padding in their
existing reserved words. Original targets retain their old absolute slots.
Fixed-zero records, including the already counted ruler, are preserved. -/
namespace Blotto.GeneralPaperHeaderCountExpansion
open GeneralPaperReferenceRegionSlots GeneralPaperSequentialLayout
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def words (A fixed count : ℕ) : List (FixedBinaryWord A) :=
  FixedBinaryWord.ofNat A count :: List.replicate (fixed - 1) (FixedBinaryWord.ofNat A 0)

def expanded {A : ℕ} (header : Header A) : Header A :=
  if header.fixed = 0 then header else ⟨header.region,0,words A header.fixed header.targets.length ++ header.targets⟩

def run (model : RationalCostModel) (S A : ℕ) (header : Header A) : Header A × ℕ :=
  if header.fixed = 0 then (header,GeneralPaperEncodedScalarStorage.natBits header.fixed + 64 * (S + A + 1)) else
    let copied := GeneralPaperHeaderTargetCopy.run model S A header.targets
    let count := GeneralPaperStoredWordEncoding.word model S A copied.count
    let zero := GeneralPaperStoredWordEncoding.word model S A 0
    let padding := GeneralPaperHeaderTargetCopy.padding S A zero.1 (header.fixed - 1)
    let combined := GeneralPaperHeaderTargetCopy.append S A (count.1 :: padding.1) copied.values
    (⟨header.region,0,combined.1⟩,copied.work + count.2 + zero.2 + padding.2 + combined.2 +
      GeneralPaperLastRegionSelection.price S A header.region + GeneralPaperEncodedScalarStorage.natBits header.fixed + 128 * (S + A + 1))

theorem data (model : RationalCostModel) (S A : ℕ) (header : Header A) : (run model S A header).1 = expanded header := by
  by_cases hf : header.fixed = 0
  · simp only [run,expanded,hf,ite_true]
  · simp only [run,expanded,hf,ite_false,GeneralPaperHeaderTargetCopy.data,GeneralPaperHeaderTargetCopy.count,
      GeneralPaperStoredWordEncoding.word_data,GeneralPaperHeaderTargetCopy.padding_data,GeneralPaperHeaderTargetCopy.append_data,words]

theorem region {A : ℕ} (header : Header A) : (expanded header).region = header.region := by
  by_cases hf : header.fixed = 0 <;> simp only [expanded,hf,ite_true,ite_false]

theorem zero_fixed {A : ℕ} (header : Header A) (hf : header.fixed = 0) : expanded header = header := by
  simp only [expanded,hf,ite_true]

theorem words_length (A fixed count : ℕ) (hf : fixed ≠ 0) : (words A fixed count).length = fixed := by
  simp only [words,List.length_cons,List.length_replicate]
  omega

theorem length {A : ℕ} (header : Header A) (hf : header.fixed ≠ 0) :
    (expanded header).targets.length = header.fixed + header.targets.length := by
  simp only [expanded,hf,ite_false,List.length_append,words_length A header.fixed header.targets.length hf]

theorem valid {A : ℕ} (header : Header A) (hValid : Valid header) : Valid (expanded header) := by
  by_cases hf : header.fixed = 0
  · rw [zero_fixed header hf]; exact hValid
  · unfold Valid
    rw [region,length header hf]
    simpa only [Valid,expanded,hf,ite_false,Nat.zero_add] using hValid

theorem target_lookup {A : ℕ} (header : Header A) (hf : header.fixed ≠ 0) (index : Fin header.targets.length) :
    (expanded header).targets[header.fixed + index.val]? = some header.targets[index.val] := by
  simp only [expanded,hf,ite_false]
  rw [List.getElem?_append_right (by rw [words_length A header.fixed header.targets.length hf]; omega)]
  rw [words_length A header.fixed header.targets.length hf]
  simp only [Nat.add_sub_cancel_left,List.getElem?_eq_getElem index.isLt]

theorem count_lookup {A : ℕ} (header : Header A) (hf : header.fixed ≠ 0) :
    (expanded header).targets[0]? = some (FixedBinaryWord.ofNat A header.targets.length) := by
  simp only [expanded,hf,ite_false]
  rw [List.getElem?_append_left (by rw [words_length A header.fixed header.targets.length hf]; omega)]
  rfl

theorem count_fits {A : ℕ} (header : Header A) (hA : 0 < A) (hValid : Valid header) (hCap : header.region.stop < 2 ^ A) :
    header.targets.length < 2 ^ A := by
  have hn : header.targets.length ≤ A * header.targets.length := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right header.targets.length (Nat.succ_le_of_lt hA)
  unfold Valid Region.stop at *
  nlinarith

theorem work_positive (model : RationalCostModel) (S A : ℕ) (header : Header A) (hf : header.fixed ≠ 0) :
    (run model S A header).2 = GeneralPaperHeaderTargetCopy.price model S A header.targets.length +
      (GeneralPaperStoredWordEncoding.word model S A header.targets.length).2 + (GeneralPaperStoredWordEncoding.word model S A 0).2 +
      (header.fixed - 1) * (A + 64 * (S + A + 1)) + header.fixed * (A + 64 * (S + A + 1)) +
      GeneralPaperLastRegionSelection.price S A header.region + GeneralPaperEncodedScalarStorage.natBits header.fixed + 256 * (S + A + 1) := by
  simp only [run,hf,ite_false,GeneralPaperHeaderTargetCopy.work,GeneralPaperHeaderTargetCopy.count,
    GeneralPaperHeaderTargetCopy.padding_work,GeneralPaperHeaderTargetCopy.append_work,
    GeneralPaperHeaderTargetCopy.padding_data,List.length_cons,List.length_replicate]
  have he : header.fixed - 1 + 1 = header.fixed := by omega
  rw [he]
  ring

end Blotto.GeneralPaperHeaderCountExpansion
