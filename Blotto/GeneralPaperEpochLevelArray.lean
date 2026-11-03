import Blotto.GeneralPaperEpochTreeHistory
import Blotto.PaperIndexedArrayConstruction

/-! Exact local levels in native indexed arrays. Every epoch initializes
zero once, then adds the materialized local increment array each round.
The operation count here is the paper's unit-cost indexed source profile;
primitive bit prices and simultaneous array lifetime remain separate.
-/
namespace Blotto.GeneralPaperEpochLevelArray
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000

def initial (n : ℕ) : FixedArrayTable n ℕ × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun _ => (0,8))

def advance {n : ℕ} (current delta : FixedArrayTable n ℕ) : FixedArrayTable n ℕ × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun i => (current.read i+delta.read i,12))

def execute {n : ℕ} (delta : ℕ → FixedArrayTable n ℕ) : ℕ → FixedArrayTable n ℕ × ℕ
  | 0 => initial n
  | t+1 =>
    let previous := execute delta t
    let updated := advance previous.1 (delta t)
    (updated.1,previous.2+updated.2+8)

theorem initialize_read (n : ℕ) (i : Fin n) : (initial n).1.read i=0 := by
  rw [initial,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]

theorem advance_read {n : ℕ} (current delta : FixedArrayTable n ℕ) (i : Fin n) :
    (advance current delta).1.read i=current.read i+delta.read i := by
  rw [advance,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]

theorem execute_read {n : ℕ} (delta : ℕ → FixedArrayTable n ℕ) (t : ℕ) (i : Fin n) :
    (execute delta t).1.read i=GeneralPaperGeometricLevels.levels (fun t i => (delta t).read i) t i := by
  induction t with
  | zero => exact initialize_read n i
  | succ t ih =>
    dsimp only [execute]
    rw [advance_read,ih]
    rfl

theorem overhead (n k : ℕ) : PaperIndexedArrayConstruction.overhead (fun _ => 1) 1 n k=18+42*k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [PaperIndexedArrayConstruction.overhead,ih]
    dsimp only [PaperIndexedArrayConstruction.stepWork]
    omega

theorem initialize_work (n : ℕ) : (initial n).2=50*n+18 := by
  rw [initial,PaperIndexedArrayConstruction.run_work,overhead]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  omega

theorem advance_work {n : ℕ} (current delta : FixedArrayTable n ℕ) : (advance current delta).2=54*n+18 := by
  rw [advance,PaperIndexedArrayConstruction.run_work,overhead]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  omega

theorem execute_work {n : ℕ} (delta : ℕ → FixedArrayTable n ℕ) (t : ℕ) :
    (execute delta t).2=50*n+18+t*(54*n+26) := by
  induction t with
  | zero => simpa only [execute,Nat.zero_mul,Nat.add_zero] using initialize_work n
  | succ t ih =>
    dsimp only [execute]
    rw [advance_work,ih]
    ring

theorem levels_agree {n m : ℕ} (left : ℕ → Fin n → ℕ) (right : ℕ → Fin m → ℕ)
    (t : ℕ) (i : Fin n) (j : Fin m) (h : ∀ r<t, left r i=right r j) :
    GeneralPaperGeometricLevels.levels left t i=GeneralPaperGeometricLevels.levels right t j := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change GeneralPaperGeometricLevels.levels left t i+left t i=
      GeneralPaperGeometricLevels.levels right t j+right t j
    rw [ih (fun r hr => h r (by omega)),h t (by omega)]

theorem cached_read {n m : ℕ} (delta : ℕ → FixedArrayTable n ℕ) (rowIncrement : ℕ → Fin m → ℕ)
    (location : Fin n → Fin m) (start count : ℕ)
    (hDelta : ∀ t<count, ∀ r, (delta t).read r=rowIncrement (start+t) (location r)) (r : Fin n) :
    (execute delta count).1.read r=GeneralPaperGeometricLevels.levels (fun t => rowIncrement (start+t)) count (location r) := by
  rw [execute_read]
  exact levels_agree _ _ count r (location r) (fun t ht => hDelta t ht r)

theorem level_bound {n : ℕ} (delta : ℕ → FixedArrayTable n ℕ) (bound count : ℕ)
    (hDelta : ∀ t r, (delta t).read r≤bound) (r : Fin n) : (execute delta count).1.read r≤count*bound := by
  rw [execute_read]
  exact GeneralPaperGeometricLevels.levels_bound _ bound count hDelta r

end Blotto.GeneralPaperEpochLevelArray
