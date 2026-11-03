import Blotto.PlayerSpecificSortWork
import Blotto.GeneralPaperNativeRepresentativeSort

/-! Actual rational ratio-table construction and stable sorted field
references. The real-RAM interpretation charges unit rational arithmetic,
indexed loads/stores and control; finite-bit prices are a later join. -/
namespace Blotto.PlayerSpecificRatioSort
set_option autoImplicit false
set_option maxHeartbeats 2500000

def callback {n : ℕ} (v w : FixedArrayTable n ℚ) (j : Fin n) : ℚ×ℕ :=
  let first := v.read j
  let second := w.read j
  (first/second,12)

def prepare {n : ℕ} (v w : FixedArrayTable n ℚ) : FixedArrayTable n ℚ×ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (callback v w)

theorem ratio_read {n : ℕ} (v w : FixedArrayTable n ℚ) (j : Fin n) :
    (prepare v w).1.read j=v.read j/w.read j := by
  unfold prepare
  rw [PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  rfl

def run {n : ℕ} (v w : FixedArrayTable n ℚ) : FixedArrayTable n (Fin n)×ℕ :=
  let ratios := prepare v w
  let sorted := GeneralPaperNativeRepresentativeSort.run (fun _ => 1) (fun _ => 1) 1 ratios.1
  (sorted.1,ratios.2+sorted.2+16)

theorem data {n : ℕ} (v w : FixedArrayTable n ℚ) :
    (run v w).1=GeneralPaperRowSort.order (prepare v w).1 :=
  GeneralPaperNativeRepresentativeSort.data (fun _ => 1) (fun _ => 1) 1 _

theorem bijective {n : ℕ} (v w : FixedArrayTable n ℚ) : Function.Bijective (run v w).1.read := by
  rw [data]
  exact ⟨GeneralPaperRowSort.order_injective _,GeneralPaperRowSort.order_surjective _⟩

theorem ordered {n : ℕ} (v w : FixedArrayTable n ℚ) :
    Monotone (fun r => v.read ((run v w).1.read r)/w.read ((run v w).1.read r)) := by
  have h := GeneralPaperRowSort.order_value_mono (prepare v w).1
  simp only [ratio_read] at h
  rw [data]
  exact h

theorem preparation_work {n : ℕ} (v w : FixedArrayTable n ℚ) :
    (prepare v w).2≤60*(n+1) := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 12 (callback v w)
    (by decide) (fun _ _ => le_rfl) (fun _ => le_rfl)
  change (prepare v w).2≤n*12+44*(n+1)*1 at h
  omega

theorem native_sort_work {n : ℕ} (values : FixedArrayTable n ℚ) :
    (GeneralPaperNativeRepresentativeSort.run (fun _ => 1) (fun _ => 1) 1 values).2≤
      594*(n+1)*(binaryWordWidth (n+1)+2)+80*(n+1) := by
  let compare := GeneralPaperNativeRepresentativeSort.compare (fun _ => 1) (fun _ => 1) 1 values
  have hc : ∀ a b : Fin n,(compare a b).2≤82 := fun _ _ => le_rfl
  have hs := PlayerSpecificSortWork.real_work compare 82 (List.finRange n) (fun a _ b _ => hc a b)
  have hl := GeneralPaperControlArrayPrice.list_work (fun _ => 1) 1
    (GeneralPaperPricedSort.run compare 1 (List.finRange n)).1 (by decide) (fun _ _ => le_rfl)
  rw [GeneralPaperPricedSort.length,List.length_finRange] at hl
  rw [List.length_finRange] at hs
  change (GeneralPaperPricedSort.run compare 1 (List.finRange n)).2+
    (PaperListReferenceArray.run (fun _ => 1) 1 (GeneralPaperPricedSort.run compare 1 (List.finRange n)).1).2+
      (16*n+16)*1≤_
  nlinarith only [hs,hl]

theorem work {n : ℕ} (v w : FixedArrayTable n ℚ) :
    (run v w).2≤1024*(n+1)*(binaryWordWidth (n+1)+2) := by
  have hp := preparation_work v w
  have hs := native_sort_work (prepare v w).1
  have hn : 1≤n+1 := by omega
  have hL := Nat.mul_le_mul_left (n+1) (by omega : 2≤binaryWordWidth (n+1)+2)
  change (prepare v w).2+
    (GeneralPaperNativeRepresentativeSort.run (fun _ => 1) (fun _ => 1) 1 (prepare v w).1).2+16≤_
  nlinarith only [hp,hs,hn,hL]

end Blotto.PlayerSpecificRatioSort
