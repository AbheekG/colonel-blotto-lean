import Blotto.GeneralPaperCataloguePointOperands

/-! Complete reference-list conversion and projected-successor map prices.
Both source traversals are called once, and the stored descriptor supplies
the input size. Reference-prefix bounds cover the conversion's own cursor.
-/
namespace Blotto.GeneralPaperCataloguePointPrice
open GeneralPaperCataloguePointExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def profile (primitive : ℕ → ℕ) (W n U : ℕ) : ℕ :=
  16*(n+1)*arrayWord W (n+2)+(5*primitive (GeneralPaperCataloguePointOperands.width U)+72*W)*n+66*W

def arithmeticProfile (n : ℕ) : ℕ := 16*(n+1)+77*n+66

theorem list_bit_work (W n : ℕ) :
    StoredArrayReferenceList.work (fun w => w) (arrayWord W (n+2)) n≤16*(n+1)*arrayWord W (n+2) := by
  let A := arrayWord W (n+2)
  have hA : 1≤A := GeneralPaperSummaryArrayControls.array_word_positive W (n+2)
  have hIndex : binaryWordWidth n+1≤A := by
    have h := binaryWordWidth_mono (show n≤n+2+1 by omega)
    unfold A arrayWord
    omega
  have h := StoredArrayReferenceList.work_bound (fun w => w) 1 (fun _ => by omega) A n
  have hMul := Nat.mul_le_mul_left n hIndex
  have hUnit := Nat.mul_le_mul_left n hA
  change _≤16*(n+1)*A
  nlinarith only [h,hMul,hUnit,hA]

theorem list_arithmetic_work (n : ℕ) : StoredArrayReferenceList.work (fun _ => 1) 1 n≤16*(n+1) := by
  induction n with
  | zero => change 2≤16; omega
  | succ n ih =>
    rw [StoredArrayReferenceList.work]
    change StoredArrayReferenceList.work (fun _ => 1) 1 n+10≤16*(n+1+1)
    omega

theorem bit_work {n : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W U : ℕ) (summary : FixedArrayTable n ℕ)
    (hCodes : ∀ r,summary.read r<2*U) :
    (run true (fun w => w) primitive W U summary).2≤profile primitive W n U := by
  let values := StoredArrayReferenceList.list summary.data
  let mapped := GeneralPaperPricedListMap.run W (successor primitive W U) values
  have hValues : ∀ code∈values,code<2*U := by
    intro code hCode
    apply member_code U summary hCodes code
    simpa only [values,StoredArrayReferenceList.list_data] using hCode
  have hLength : values.length=n := by
    dsimp only [values]
    rw [StoredArrayReferenceList.list_data,Array.length_toList,summary.size]
  have hMap := GeneralPaperPricedListMap.work W (5*primitive (GeneralPaperCataloguePointOperands.width U)+64*W)
    (successor primitive W U) values (fun code hc => GeneralPaperCataloguePointOperands.successor_work primitive hMono W U code (hValues code hc))
  rw [hLength] at hMap
  have hList := list_bit_work W n
  have hListSource : StoredArrayReferenceList.work (fun w => w) (arrayWord W (n+2)) summary.data.size≤
      16*(n+1)*arrayWord W (n+2) := by simpa only [summary.size] using hList
  change mapped.2≤_ at hMap
  have hTotal := Nat.add_le_add_right (Nat.add_le_add hListSource hMap) (64*W)
  exact hTotal.trans_eq (by unfold profile; ring)

theorem arithmetic_work {n : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) (hCodes : ∀ r,summary.read r<2*U) :
    (run false (fun _ => 1) (fun _ => 1) 1 U summary).2≤arithmeticProfile n := by
  let values := StoredArrayReferenceList.list summary.data
  let mapped := GeneralPaperPricedListMap.run 1 (successor (fun _ => 1) 1 U) values
  have hValues : ∀ code∈values,code<2*U := by
    intro code hCode
    apply member_code U summary hCodes code
    simpa only [values,StoredArrayReferenceList.list_data] using hCode
  have hLength : values.length=n := by
    dsimp only [values]
    rw [StoredArrayReferenceList.list_data,Array.length_toList,summary.size]
  have hMap := GeneralPaperPricedListMap.work 1 69 (successor (fun _ => 1) 1 U) values
    (fun code hc => GeneralPaperCataloguePointOperands.successor_work (fun _ => 1) (fun _ _ _ => Nat.le_refl 1) 1 U code (hValues code hc))
  rw [hLength] at hMap
  have hList := list_arithmetic_work n
  have hListSource : StoredArrayReferenceList.work (fun _ => 1) 1 summary.data.size≤16*(n+1) := by
    simpa only [summary.size] using hList
  change mapped.2≤_ at hMap
  have hTotal := Nat.add_le_add_right (Nat.add_le_add hListSource hMap) 64
  exact hTotal.trans_eq (by unfold arithmeticProfile; ring)

theorem every_prefix_references {n : ℕ} (summary : FixedArrayTable n ℕ) (used : ℕ) :
    n+2*(StoredArrayReferenceList.advance summary.data used ⟨summary.data.size,Nat.le_refl _,[]⟩).tail.length≤3*n := by
  have h := StoredArrayReferenceList.every_prefix_references summary.data used ⟨summary.data.size,Nat.le_refl _,[]⟩
  simpa only [summary.size,List.length_nil,Nat.mul_zero,Nat.add_zero] using h

theorem every_prefix_counter {n : ℕ} (summary : FixedArrayTable n ℕ) (used : ℕ) :
    binaryWordWidth (StoredArrayReferenceList.advance summary.data used ⟨summary.data.size,Nat.le_refl _,[]⟩).remaining≤binaryWordWidth n := by
  have h := StoredArrayReferenceList.every_prefix_counter_width summary.data used ⟨summary.data.size,Nat.le_refl _,[]⟩
  simpa only [summary.size] using h

end Blotto.GeneralPaperCataloguePointPrice
