import Blotto.PRGPaperSharpDrawCost

/-! Indexed construction in the paper's mutable-reference-array model.
Each callback is invoked once and brings its own already-priced source work.
The loop additionally charges index/control words, reference loads/writes,
the array descriptor and returns. A source push stores one reference; this
does not calibrate Lean Array.push, persistent copying or a native allocator.
-/

namespace Blotto.PaperIndexedArrayConstruction
open scoped BigOperators
set_option autoImplicit false

def stepWork (primitive : ℕ → ℕ) (addressWidth index : ℕ) : ℕ :=
  6*addressWidth+8*primitive (binaryWordWidth (index+1))+28

def initialWork (primitive : ℕ → ℕ) (addressWidth count : ℕ) : ℕ :=
  4*addressWidth+2*primitive (binaryWordWidth (count+1))+12

def overhead (primitive : ℕ → ℕ) (addressWidth count : ℕ) : ℕ → ℕ
  | 0 => initialWork primitive addressWidth count
  | k+1 => overhead primitive addressWidth count k+stepWork primitive addressWidth k

def fill {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (addressWidth : ℕ)
    (callback : Fin n → α × ℕ) : (k : ℕ) → k ≤ n → Array α × ℕ
  | 0,_ => (#[],initialWork primitive addressWidth n)
  | k+1,hk =>
      let earlier := fill primitive addressWidth callback k (by omega)
      let current := callback ⟨k,by omega⟩
      (earlier.1.push current.1,earlier.2+current.2+stepWork primitive addressWidth k)

theorem fill_data {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (addressWidth : ℕ)
    (callback : Fin n → α × ℕ) (k : ℕ) (hk : k ≤ n) :
    (fill primitive addressWidth callback k hk).1 =
      Array.ofFn (fun j : Fin k => (callback ⟨j.val,by omega⟩).1) := by
  induction k with
  | zero => simp only [fill,Array.ofFn_zero]
  | succ k ih =>
      rw [fill]
      dsimp only
      rw [ih (by omega),Array.ofFn_succ]
      rfl

theorem fill_work {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (addressWidth : ℕ)
    (callback : Fin n → α × ℕ) (k : ℕ) (hk : k ≤ n) :
    (fill primitive addressWidth callback k hk).2 =
      (∑ j : Fin k,(callback ⟨j.val,by omega⟩).2)+overhead primitive addressWidth n k := by
  induction k with
  | zero => simp only [fill,Finset.univ_eq_empty,Finset.sum_empty,zero_add,overhead]
  | succ k ih =>
      rw [fill]
      dsimp only
      rw [ih (by omega),Fin.sum_univ_castSucc,overhead]
      simp only [Fin.val_castSucc,Fin.val_last]
      ring

def run {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (addressWidth : ℕ)
    (callback : Fin n → α × ℕ) : FixedArrayTable n α × ℕ :=
  let returned := fill primitive addressWidth callback n le_rfl
  (⟨returned.1,by rw [fill_data,Array.size_ofFn]⟩,returned.2)

theorem run_data {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (addressWidth : ℕ)
    (callback : Fin n → α × ℕ) :
    (run primitive addressWidth callback).1 = FixedArrayTable.ofFn (fun j => (callback j).1) := by
  unfold run FixedArrayTable.ofFn
  dsimp only
  congr 1
  exact fill_data primitive addressWidth callback n le_rfl

theorem run_work {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (addressWidth : ℕ)
    (callback : Fin n → α × ℕ) :
    (run primitive addressWidth callback).2 =
      (∑ j,(callback j).2)+overhead primitive addressWidth n n :=
  fill_work primitive addressWidth callback n le_rfl

theorem overhead_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w)
    (addressWidth count k : ℕ) (hk : k ≤ count) :
    overhead primitive addressWidth count k ≤
      (k+1)*(6*addressWidth+10*c*binaryWordWidth (count+1)+28) := by
  have hInitial := hPrimitive (binaryWordWidth (count+1))
  induction k with
  | zero =>
      simp only [overhead,initialWork,Nat.zero_add,Nat.one_mul]
      nlinarith only [hInitial]
  | succ k ih =>
      have hStep := (hPrimitive (binaryWordWidth (k+1))).trans
        (Nat.mul_le_mul_left c (binaryWordWidth_mono (by omega : k+1 ≤ count+1)))
      have hEarlier := ih (by omega)
      simp only [overhead,stepWork]
      nlinarith only [hEarlier,hStep]

theorem run_work_bound {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w,primitive w ≤ c*w) (addressWidth : ℕ) (callback : Fin n → α × ℕ) :
    (run primitive addressWidth callback).2 ≤ (∑ j,(callback j).2)+
      (n+1)*(6*addressWidth+10*c*binaryWordWidth (n+1)+28) := by
  rw [run_work]
  exact Nat.add_le_add_left (overhead_bound primitive c hPrimitive addressWidth n n le_rfl) _

theorem pool_overhead_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w)
    (n W : ℕ) (hn : n ≤ W) :
    overhead primitive (StoredArrayReferenceList.poolAddressWidth n W) n n ≤
      64*(c+1)*(n+1)*(binaryWordWidth (W+2)+1) := by
  let Q := binaryWordWidth (W+2)+1
  have hQ : 1 ≤ Q := by dsimp [Q]; omega
  have hIndex : binaryWordWidth (n+1) ≤ Q :=
    (binaryWordWidth_mono (by omega : n+1 ≤ W+2)).trans (Nat.le_succ _)
  have hWord : binaryWordWidth (W+1) ≤ Q :=
    (binaryWordWidth_mono (by omega : W+1 ≤ W+2)).trans (Nat.le_succ _)
  have hAddress := StoredArrayReferenceList.poolAddressWidth_log_bound n W
  have hA : StoredArrayReferenceList.poolAddressWidth n W ≤ 2*Q := by omega
  have hPay := Nat.mul_le_mul_left (10*c) hIndex
  have hStep : 6*StoredArrayReferenceList.poolAddressWidth n W+10*c*binaryWordWidth (n+1)+28 ≤
      64*(c+1)*Q := by nlinarith only [hA,hPay,hQ]
  have hTotal := Nat.mul_le_mul_left (n+1) hStep
  exact (overhead_bound primitive c hPrimitive _ n n le_rfl).trans
    (by simpa only [Q,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hTotal)

end Blotto.PaperIndexedArrayConstruction
