import Blotto.GeneralPaperNativeRationalCircleLaw

/-! Native streaming selected-entry writes in the declared mutable-array
paper model. Each callback constructs and prices its key/value once. The
output array is threaded linearly; no search or inverse map is executed. -/
namespace Blotto.GeneralPaperIndexedScatter
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2200000

def fill {n m : ℕ} {α : Type*} (index : ℕ → ℕ) (A : ℕ)
    (evaluate : Fin m → (Fin n×α)×ℕ) : (k : ℕ) → k≤m → FixedArrayTable n α → FixedArrayTable n α × ℕ
  | 0,_,table => (table,16*A)
  | k+1,hk,table =>
    let old := fill index A evaluate k (by omega) table
    let current := evaluate ⟨k,by omega⟩
    (old.1.write current.1.1 current.1.2,old.2+current.2+PaperIndexedArrayConstruction.stepWork index A k+32*A)

theorem fill_read_at {n m : ℕ} {α : Type*} (index : ℕ → ℕ) (A : ℕ)
    (evaluate : Fin m → (Fin n×α)×ℕ) (hInjective : Function.Injective (fun i => (evaluate i).1.1))
    (k : ℕ) (hk : k≤m) (table : FixedArrayTable n α) (i : Fin k) :
    (fill index A evaluate k hk table).1.read (evaluate ⟨i.val,by omega⟩).1.1=(evaluate ⟨i.val,by omega⟩).1.2 := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    rw [fill]
    dsimp only
    rw [FixedArrayTable.read_write]
    by_cases he:(evaluate ⟨i.val,by omega⟩).1.1=(evaluate ⟨k,by omega⟩).1.1
    · rw [ite_eq_left he]
      exact congrArg (fun j => (evaluate j).1.2) (hInjective he).symm
    · rw [ite_eq_right he]
      have hi : i.val≠k := by
        intro hi
        apply he
        exact congrArg (fun j => (evaluate j).1.1) (Fin.ext hi)
      exact ih (by omega) ⟨i.val,by omega⟩

theorem fill_preserves {n m : ℕ} {α : Type*} (index : ℕ → ℕ) (A : ℕ)
    (evaluate : Fin m → (Fin n×α)×ℕ) (k : ℕ) (hk : k≤m) (table : FixedArrayTable n α) (j : Fin n)
    (hAvoid : ∀ i:Fin k,(evaluate ⟨i.val,by omega⟩).1.1≠j) :
    (fill index A evaluate k hk table).1.read j=table.read j := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [fill]
    dsimp only
    rw [FixedArrayTable.read_write,ite_eq_right (Ne.symm (hAvoid ⟨k,by omega⟩))]
    exact ih (by omega) (fun i => hAvoid i.castSucc)

theorem fill_work {n m : ℕ} {α : Type*} (index : ℕ → ℕ) (A C : ℕ) (hA : 1≤A)
    (evaluate : Fin m → (Fin n×α)×ℕ) (hC : ∀ i,(evaluate i).2≤C)
    (hIndex : ∀ i≤m,index (binaryWordWidth (i+1))≤A)
    (k : ℕ) (hk : k≤m) (table : FixedArrayTable n α) :
    (fill index A evaluate k hk table).2≤k*C+96*(k+1)*A := by
  induction k with
  | zero => simp only [fill];omega
  | succ k ih =>
    have hi := ih (by omega)
    have he := hC ⟨k,by omega⟩
    have hc := hIndex k (by omega)
    change (fill index A evaluate k (by omega) table).2+(evaluate ⟨k,by omega⟩).2+
      PaperIndexedArrayConstruction.stepWork index A k+32*A≤_
    unfold PaperIndexedArrayConstruction.stepWork
    nlinarith only [hi,he,hc,hA]

def run {n m : ℕ} {α : Type*} (index : ℕ → ℕ) (A : ℕ) (default : α)
    (evaluate : Fin m → (Fin n×α)×ℕ) : FixedArrayTable n α × ℕ :=
  let initial := PaperIndexedArrayConstruction.run index A (fun _:Fin n => (default,32*A))
  let result := fill index A evaluate m le_rfl initial.1
  (result.1,initial.2+result.2+16*A)

theorem read_at {n m : ℕ} {α : Type*} (index : ℕ → ℕ) (A : ℕ) (default : α)
    (evaluate : Fin m → (Fin n×α)×ℕ) (hInjective : Function.Injective (fun i => (evaluate i).1.1)) (i : Fin m) :
    (run index A default evaluate).1.read (evaluate i).1.1=(evaluate i).1.2 :=
  fill_read_at index A evaluate hInjective m le_rfl _ i

theorem fill_data_congr {n m : ℕ} {α : Type*} (index index' : ℕ → ℕ) (A A' : ℕ)
    (evaluate evaluate' : Fin m → (Fin n×α)×ℕ) (h : ∀ i,(evaluate i).1=(evaluate' i).1)
    (k : ℕ) (hk : k≤m) (table : FixedArrayTable n α) :
    (fill index A evaluate k hk table).1=(fill index' A' evaluate' k hk table).1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp only [fill]
    rw [ih (by omega),h]

theorem data_congr {n m : ℕ} {α : Type*} (index index' : ℕ → ℕ) (A A' : ℕ) (default : α)
    (evaluate evaluate' : Fin m → (Fin n×α)×ℕ) (h : ∀ i,(evaluate i).1=(evaluate' i).1) :
    (run index A default evaluate).1=(run index' A' default evaluate').1 := by
  unfold run
  dsimp only
  rw [PaperIndexedArrayConstruction.run_data,PaperIndexedArrayConstruction.run_data]
  exact fill_data_congr index index' A A' evaluate evaluate' h m le_rfl _

theorem work {n m : ℕ} {α : Type*} (index : ℕ → ℕ) (A C : ℕ) (hA : 1≤A) (default : α)
    (evaluate : Fin m → (Fin n×α)×ℕ) (hC : ∀ i,(evaluate i).2≤C)
    (hIndex : ∀ i≤n+m,index (binaryWordWidth (i+1))≤A) :
    (run index A default evaluate).2≤m*C+192*(n+m+1)*A := by
  have hInitial := GeneralPaperControlArrayPrice.indexed_work index A (32*A) (fun _:Fin n => (default,32*A))
    hA (fun i hi => hIndex i (by omega)) (fun _ => le_rfl)
  have hFill := fill_work index A C hA evaluate hC (fun i hi => hIndex i (by omega)) m le_rfl
    (PaperIndexedArrayConstruction.run index A (fun _:Fin n => (default,32*A))).1
  change (PaperIndexedArrayConstruction.run index A (fun _:Fin n => (default,32*A))).2+
    (fill index A evaluate m le_rfl (PaperIndexedArrayConstruction.run index A (fun _:Fin n => (default,32*A))).1).2+16*A≤_
  nlinarith only [hInitial,hFill]

end Blotto.GeneralPaperIndexedScatter
