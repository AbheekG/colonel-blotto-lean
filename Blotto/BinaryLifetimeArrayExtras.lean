import Blotto.BinaryLifetimeArrayMeasured

/-! One-pass callback enumeration and array packing retain callback metadata.
The first field is the exact previous measured build for the projected callback.
Metadata aggregation/evaluation and native ownership costs need separate prices. -/
namespace Blotto.BinaryLifetimeArrayExtras
open BinarySeedPreparationSpace
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000

def enumerate {α : Type*} : (n : ℕ) → (Fin n → ((α × Trace) × ℕ) × ℕ) → (List (α × Trace) × ℕ) × ℕ
  | 0,_ => (([],4),0)
  | n+1,produce =>
      let first := produce 0
      let later := enumerate n (fun j => produce j.succ)
      ((first.1.1::later.1.1,first.1.2+later.1.2+(n+1)+8),first.2+later.2)

theorem enumerate_record {α : Type*} (n : ℕ) (produce : Fin n → ((α × Trace) × ℕ) × ℕ) :
    (enumerate n produce).1 = BinaryLifetimeArrayMeasured.enumerate n (fun j => (produce j).1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [enumerate,BinaryLifetimeArrayMeasured.enumerate,ih]

theorem enumerate_extra {α : Type*} (n : ℕ) (produce : Fin n → ((α × Trace) × ℕ) × ℕ) :
    (enumerate n produce).2 = ∑ j, (produce j).2 := by
  induction n with
  | zero => simp only [enumerate,Fin.sum_univ_zero]
  | succ n ih => simp only [enumerate,ih,Fin.sum_univ_succ]

theorem enumerate_bound {α : Type*} (n : ℕ) (produce : Fin n → ((α × Trace) × ℕ) × ℕ)
    (C : ℕ) (h : ∀ j,(produce j).2 ≤ C*(produce j).1.2) :
    (enumerate n produce).2 ≤ C*(enumerate n produce).1.2 := by
  rw [enumerate_extra,enumerate_record,BinaryLifetimeArrayMeasured.enumerate_work]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => h j)
  rw [← Finset.mul_sum] at hs
  exact hs.trans (Nat.mul_le_mul_left C (Nat.le_add_right _ _))

def build {α : Type*} (n : ℕ) (produce : Fin n → ((α × Trace) × ℕ) × ℕ) : ((FixedArrayTable n α × Trace) × ℕ) × ℕ :=
  let produced := enumerate n produce
  let entries := produced.1
  let values := BinaryLifetimeArray.mapWithVisits Prod.fst entries.1
  let packed := BinaryLifetimeArrayMeasured.pack values.1 (Array.mkEmpty n)
  have hSize : packed.1.size = n := by
    simp [packed,BinaryLifetimeArrayMeasured.pack_state,values,entries,produced,
      enumerate_record,BinaryLifetimeArray.mapWithVisits_state,BinaryLifetimeArrayMeasured.enumerate_state]
  (((⟨packed.1,hSize⟩,[.frames (2*n+8),.arrayAllocation (BinaryLifetimeArrayMeasured.storageReserve n)]++
    under (n+2) (BinaryLifetimeFlattenList.flattenDirect (BinaryLifetimeArray.mapDirect Prod.snd entries.1))),
    entries.2+4*values.2+packed.2+8),produced.2)

theorem build_record {α : Type*} (n : ℕ) (produce : Fin n → ((α × Trace) × ℕ) × ℕ) :
    (build n produce).1 = BinaryLifetimeArrayMeasured.build n (fun j => (produce j).1) := by
  simp only [build,enumerate_record,BinaryLifetimeArrayMeasured.build]

theorem build_extra {α : Type*} (n : ℕ) (produce : Fin n → ((α × Trace) × ℕ) × ℕ) :
    (build n produce).2 = ∑ j, (produce j).2 := by
  simpa only [build] using enumerate_extra n produce

theorem build_bound {α : Type*} (n : ℕ) (produce : Fin n → ((α × Trace) × ℕ) × ℕ)
    (C : ℕ) (h : ∀ j,(produce j).2 ≤ C*(produce j).1.2) :
    (build n produce).2 ≤ C*(build n produce).1.2 := by
  have he := enumerate_bound n produce C h
  dsimp only [build]
  exact he.trans (Nat.mul_le_mul_left C (by omega))

end Blotto.BinaryLifetimeArrayExtras
