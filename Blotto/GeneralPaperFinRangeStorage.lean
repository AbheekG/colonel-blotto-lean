import Blotto.GeneralPaperPricedListStreamStorage

/-! Stock finite-index iterator construction in the paper list model.
Natural and finite-index cells, a borrowed copied prefix, constructor/map
control frames and the native linear iterator charge are all reserved.
No integer encoding traversal or allocator calibration is executed. -/
namespace Blotto.GeneralPaperFinRangeStorage
open GeneralPaperEncodedScalarStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000

def frames (W n : ℕ) : ℕ := ∑ i : Fin (n+1), (fields W [n,i.val]+128*W)

theorem frames_bound (W n : ℕ) : frames W n≤(n+1)*(2*(natBits n+W)+160*W) := by
  have he (i : Fin (n+1)) : fields W [n,i.val]+128*W≤2*(natBits n+W)+160*W := by
    have hf := fields_bound W (natBits n) [n,i.val] (by
      intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl
      · exact le_rfl
      · exact Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1)
    change GeneralPaperEncodedScalarStorage.fields W _≤2*(natBits n+W)+32*W at hf
    omega
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => he i)
  simpa only [frames,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using h

def window (W n copied : ℕ) : ℕ :=
  listFootprint W natBits (List.range n)+listFootprint W GeneralPaperScoreSelectionStorage.labelBits (List.finRange n)+
    GeneralPaperBorrowedListStorage.footprint W ((List.finRange n).take copied)+2*frames W n+
    fields W [n,16*(n+1)*W]+256*W

def profile (W n : ℕ) : ℕ := 2*(n*(natBits n+2*W)+32*W)+(2*n*W+32*W)+
  2*((n+1)*(2*(natBits n+W)+160*W))+2*(natBits (n+16*(n+1)*W)+W)+288*W

theorem bounded (W n copied : ℕ) : window W n copied≤profile W n := by
  have hN := list_bound W (natBits n) natBits (List.range n) (by
    intro a ha
    exact Nat.add_le_add_left (binaryWordWidth_mono (List.mem_range.mp ha).le) 1)
  rw [List.length_range] at hN
  have hF := list_bound W (natBits n) GeneralPaperScoreSelectionStorage.labelBits (List.finRange n)
    (fun l _ => GeneralPaperScoreSelectionStorage.label_bound l)
  rw [List.length_finRange] at hF
  have hCopy := GeneralPaperBorrowedListStorage.bounded W n ((List.finRange n).take copied)
    (by simp only [List.length_take,List.length_finRange]; omega)
  have hFrames := frames_bound W n
  have hFields := fields_bound W (natBits (n+16*(n+1)*W)) [n,16*(n+1)*W] (by
    intro a ha
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl <;> omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤2*(natBits (n+16*(n+1)*W)+W)+32*W at hFields
  unfold window profile
  omega

end Blotto.GeneralPaperFinRangeStorage
