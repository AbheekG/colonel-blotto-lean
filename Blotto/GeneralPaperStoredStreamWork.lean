import Blotto.GeneralPaperStoredScalarReadWork

/-! Forward collection charges the sum of actual payload encodings. Every
counter prefix is bounded by the loaded extent, and only one increment,
reader call and payload/list copy are charged per successful element. -/
namespace Blotto.GeneralPaperStoredStreamWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

def stepBound (model : RationalCostModel) (A : ℕ) : ℕ := 5 * model.rat (A + 2) + 16 * A + 16

theorem increment_work (model : RationalCostModel) (A start : ℕ) (hStart : start + 1 < 2 ^ A) :
    (GeneralPaperNaturalScalarStep.run model A .add start 1).2 ≤ stepBound model A := by
  have hs : binaryWordWidth start ≤ A + 1 := binaryWordWidth_le_of_lt_pow (by omega)
    ((show start < 2 ^ A by omega).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ A)))
  have hn : binaryWordWidth (start + 1) ≤ A + 1 := binaryWordWidth_le_of_lt_pow (by omega)
    (hStart.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ A)))
  exact GeneralPaperNaturalScalarStep.work model A .add start 1 (A + 2)
    (by unfold GeneralPaperNaturalScalarStep.word; omega) (by change 2 ≤ A + 2; omega)
    (by change 1 + binaryWordWidth (start + 1) ≤ A + 2; omega)

theorem price_bound {α : Type*} (model : RationalCostModel) (A : ℕ) (reader : ℕ → Option α × ℕ) (encode : α → ℕ)
    (values : List α) (start C R : ℕ) (hEnd : start + values.length < 2 ^ A)
    (hReads : ∀ index : Fin values.length,(reader (start + index.val)).2 ≤ C * encode values[index.val] + R) :
    GeneralPaperStoredReadStream.price model A reader encode start values ≤
      (C + 1) * (values.map encode).sum + values.length * (R + stepBound model A + 128 * (A + 1)) + 64 * (A + 1) := by
  induction values generalizing start with
  | nil => simp only [GeneralPaperStoredReadStream.price,List.map_nil,List.sum_nil,List.length_nil,Nat.mul_zero,Nat.zero_mul,Nat.zero_add,le_rfl]
  | cons value values ih =>
    have hHead := hReads ⟨0,by simp only [List.length_cons]; omega⟩
    simp only [Nat.add_zero,List.getElem_cons_zero] at hHead
    have hStep := increment_work model A start (by simp only [List.length_cons] at hEnd; omega)
    have hTail : ∀ index : Fin values.length,(reader (start + 1 + index.val)).2 ≤ C * encode values[index.val] + R := by
      intro index
      have h := hReads ⟨index.val + 1,by simp only [List.length_cons]; omega⟩
      simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1 index.val] using h
    have hLater := ih (start + 1) (by simp only [List.length_cons] at hEnd; omega) hTail
    simp only [GeneralPaperStoredReadStream.price,List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [hHead,hStep,hLater]

theorem rational_array_capacity {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable n ℚ)
    (hA : 0 < A)
    (hOwner : (GeneralPaperMappedScalarArrayCursor.expected model S A start
      (source.data.toList.map GeneralPaperRetainedScalarValue.Scalar.rational)).header.region.stop < 2 ^ A) : n + 1 < 2 ^ A := by
  change start + A * (64 + (source.data.toList.map GeneralPaperRetainedScalarValue.Scalar.rational).length) < 2 ^ A at hOwner
  rw [List.length_map,Array.length_toList,source.size] at hOwner
  nlinarith only [hA,hOwner]

theorem rational_price {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (source : FixedArrayTable n ℚ)
    (hRead : GeneralPaperSamplerRecordInstallation.Readback model A installed
      (GeneralPaperFieldDirectory.ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start
        (source.data.toList.map GeneralPaperRetainedScalarValue.Scalar.rational))))
    (hRoot : installed.root = (GeneralPaperMappedScalarArrayCursor.expected model S A start
      (source.data.toList.map GeneralPaperRetainedScalarValue.Scalar.rational)).header.region.reference)
    (hCount : n < 2 ^ A) :
    GeneralPaperStoredReadStream.price model A (GeneralPaperStoredScalarRead.rational model A installed 64) rationalWordWidth 0 source.data.toList ≤
      3 * (source.data.toList.map rationalWordWidth).sum + n *
        (GeneralPaperStoredScalarReadWork.overhead model A + stepBound model A + 128 * (A + 1)) + 64 * (A + 1) := by
  have hLength : source.data.toList.length = n := by rw [Array.length_toList,source.size]
  have hReads : ∀ index : Fin source.data.toList.length,
      (GeneralPaperStoredScalarRead.rational model A installed 64 (0 + index.val)).2 ≤ 2 * rationalWordWidth source.data.toList[index.val] +
        GeneralPaperStoredScalarReadWork.overhead model A := by
    intro index
    have hi : index.val < n := by simpa only [hLength] using index.isLt
    simpa only [Nat.zero_add,Array.getElem_toList,FixedArrayTable.read] using
      GeneralPaperStoredScalarReadWork.rational_array_work model S A start installed source hRead hRoot hCount ⟨index.val,hi⟩
  simpa only [hLength] using price_bound model A _ rationalWordWidth source.data.toList 0 2
    (GeneralPaperStoredScalarReadWork.overhead model A) (by simpa only [Nat.zero_add,hLength] using hCount) hReads

end Blotto.GeneralPaperStoredStreamWork
