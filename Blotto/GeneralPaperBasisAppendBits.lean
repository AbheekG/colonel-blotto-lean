import Blotto.GeneralPaperBasisDenseBits

/-! Bit index/reference prices for original-row prefix extraction and
retained-row append. Existing dense payloads are referenced, not rebuilt.
-/
namespace Blotto.GeneralPaperBasisAppendBits
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisDenseRow
open scoped BigOperators
set_option autoImplicit false

theorem prefix_work {j d : ℕ} (W : ℕ) (hW : 1≤W) (hJ : binaryWordWidth (j+1)≤W) (row : Dense d) (hj : j≤d) :
    (GeneralPaperBasisArrayPrice.prefixRun (fun w => w) W row hj).2≤64*(j+1)*W := by
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W
    (fun i : Fin j => (row.coefficients.read (GeneralPaperBasisPrefixSum.embed hj i),4*W))
  change (GeneralPaperBasisArrayPrice.prefixRun (fun w => w) W row hj).2≤_ at hh
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hh
  have hO : 6*W+10*1*binaryWordWidth (j+1)+28≤44*W := by omega
  have ho := Nat.mul_le_mul_left (j+1) hO
  nlinarith only [hh,ho,Nat.zero_le (j*W)]

theorem append_work {j d : ℕ} (W : ℕ) (hW : 1≤W) (hJ : binaryWordWidth (j+2)≤W) (rows : Rows j d) (row : Dense d) :
    (GeneralPaperBasisArrayPrice.appendRun (fun w => w) W rows row).2≤64*(j+2)*W := by
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W
    (fun i : Fin (j+1) => (if h : i.val<j then rows.read ⟨i.val,h⟩ else row,8*W))
  change (GeneralPaperBasisArrayPrice.appendRun (fun w => w) W rows row).2≤_ at hh
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.add_assoc,Nat.reduceAdd] at hh
  have hO : 6*W+10*1*binaryWordWidth (j+2)+28≤44*W := by omega
  have ho := Nat.mul_le_mul_left (j+2) hO
  nlinarith only [hh,ho,Nat.zero_le (j*W)]

theorem initial_work (W d : ℕ) (hW : 1≤W) :
    (GeneralPaperBasisArrayPrice.initialRun (fun w => w) W d).2≤64*W := by
  change PaperIndexedArrayConstruction.overhead (fun w => w) W 0 0+
    PaperIndexedArrayConstruction.overhead (fun w => w) W 0 0+8*W≤64*W
  have hOne : binaryWordWidth (0+1)=1 := by decide
  simp only [PaperIndexedArrayConstruction.overhead,PaperIndexedArrayConstruction.initialWork,hOne]
  omega

theorem blocker_unit_terms {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (blocker : GeneralPaperRayBlockerRows.Descriptor T m K) :
    ∀ t∈(GeneralPaperRayBlockerRows.row labels blocker).terms,t.2.natAbs≤1 := by
  rcases blocker with static|tuple
  · exact GeneralPaperStaticRowPrice.unit_terms labels static
  · have hh := RationalOrderCell.unitTerms_neg _ (RationalOrderCell.rawRow_unitTerms (fun _ => 0) (.inr (tuple.read,0)))
    intro t ht
    rcases hh t ht with he|he <;> simp only [he,Int.natAbs_one,Int.natAbs_neg,le_refl]

end Blotto.GeneralPaperBasisAppendBits
