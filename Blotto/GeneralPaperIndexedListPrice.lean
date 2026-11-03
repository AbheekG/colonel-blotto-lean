import Blotto.GeneralPaperRangeUpdateBitPrice

/-! One backward indexed loop constructs a list from a retained count.
Each callback executes once; list cells retain references. There is no
intermediate index array, length traversal or work-sum replay pass.
-/
namespace Blotto.GeneralPaperIndexedListPrice
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096
variable {α : Type*}

def stepCost (index : ℕ → ℕ) (A remaining : ℕ) : ℕ :=
  8*index (binaryWordWidth (remaining+1)+1)+64*A

def fill {n : ℕ} (index : ℕ → ℕ) (A : ℕ) (callback : Fin n → α × ℕ) :
    (remaining : ℕ) → remaining≤n → List α → List α × ℕ
  | 0,_,suffix => (suffix,2*index 1+16*A)
  | remaining+1,h,suffix =>
    let item := callback ⟨remaining,by omega⟩
    let rest := fill index A callback remaining (by omega) (item.1::suffix)
    (rest.1,item.2+rest.2+stepCost index A remaining)

def run {n : ℕ} (index : ℕ → ℕ) (A : ℕ) (callback : Fin n → α × ℕ) : List α × ℕ :=
  fill index A callback n (Nat.le_refl _) []

theorem fill_data {n : ℕ} (index : ℕ → ℕ) (A : ℕ) (callback : Fin n → α × ℕ)
    (remaining : ℕ) (h : remaining≤n) (suffix : List α) :
    (fill index A callback remaining h suffix).1=
      List.ofFn (fun r : Fin remaining => (callback ⟨r.val,by omega⟩).1)++suffix := by
  induction remaining generalizing suffix with
  | zero => simp only [fill,List.ofFn_zero,List.nil_append]
  | succ remaining ih =>
    rw [fill]
    dsimp only
    rw [ih]
    conv_rhs => rw [List.ofFn_succ',List.concat_eq_append,List.append_assoc]
    rfl

theorem data {n : ℕ} (index : ℕ → ℕ) (A : ℕ) (callback : Fin n → α × ℕ) :
    (run index A callback).1=List.ofFn (fun r => (callback r).1) := by
  simp only [run,fill_data,List.append_nil]

theorem fill_work {n : ℕ} (index : ℕ → ℕ) (A C : ℕ) (callback : Fin n → α × ℕ)
    (hBase : index 1≤A) (hIndex : ∀ r<n,index (binaryWordWidth (r+1)+1)≤A)
    (hCallback : ∀ r,(callback r).2≤C) (remaining : ℕ) (h : remaining≤n) (suffix : List α) :
    (fill index A callback remaining h suffix).2≤remaining*(C+72*A)+18*A := by
  induction remaining generalizing suffix with
  | zero => change 2*index 1+16*A≤_; omega
  | succ remaining ih =>
    have hs := hIndex remaining (by omega)
    have hc := hCallback ⟨remaining,by omega⟩
    have ht := ih (by omega) ((callback ⟨remaining,by omega⟩).1::suffix)
    change (callback ⟨remaining,by omega⟩).2+
      (fill index A callback remaining (by omega) ((callback ⟨remaining,by omega⟩).1::suffix)).2+
      stepCost index A remaining≤_
    unfold stepCost
    nlinarith only [hs,hc,ht]

theorem work {n : ℕ} (index : ℕ → ℕ) (A C : ℕ) (callback : Fin n → α × ℕ)
    (hBase : index 1≤A) (hIndex : ∀ r<n,index (binaryWordWidth (r+1)+1)≤A)
    (hCallback : ∀ r,(callback r).2≤C) : (run index A callback).2≤n*(C+72*A)+18*A :=
  fill_work index A C callback hBase hIndex hCallback n (Nat.le_refl _) []

theorem every_prefix {n : ℕ} (index : ℕ → ℕ) (A : ℕ) (callback : Fin n → α × ℕ)
    (remaining : ℕ) (h : remaining≤n) (suffix : List α) :
    (fill index A callback remaining h suffix).1.length=remaining+suffix.length := by
  rw [fill_data,List.length_append,List.length_ofFn]

end Blotto.GeneralPaperIndexedListPrice
