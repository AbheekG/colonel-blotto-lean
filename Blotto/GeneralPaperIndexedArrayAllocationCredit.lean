import Blotto.GeneralPaperEqualLengthReferenceScaling

/-! Prefix payloads are covered by charged callback writes and array work.
This is the retained-buffer component only: caller ownership, activation
frames and callback scratch retain their separate lifetime obligations. -/
namespace Blotto.GeneralPaperIndexedArrayAllocationCredit
open scoped BigOperators
open GeneralPaperEncodedBasisStorage (arrayFootprint)
open GeneralPaperIndexedArrayLifetime (prefixTable)
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem overhead_lower (primitive : ℕ → ℕ) (A n k : ℕ) :
    4 * A + 6 * A * k + 12 + 28 * k ≤ PaperIndexedArrayConstruction.overhead primitive A n k := by
  induction k with
  | zero =>
    unfold PaperIndexedArrayConstruction.overhead PaperIndexedArrayConstruction.initialWork
    omega
  | succ k ih =>
    rw [PaperIndexedArrayConstruction.overhead]
    unfold PaperIndexedArrayConstruction.stepWork
    simp only [Nat.mul_succ]
    omega

theorem prefix_charged {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (A c : ℕ)
    (callback : Fin n → α × ℕ) (encode : α → ℕ) (hc : 16 ≤ c)
    (h : ∀ j, encode (callback j).1 ≤ c * (callback j).2) (k : ℕ) (hk : k ≤ n) :
    arrayFootprint A encode (prefixTable primitive A callback k hk) ≤
      c * (PaperIndexedArrayConstruction.fill primitive A callback k hk).2 := by
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin k) _ =>
    Nat.add_le_add_left (h ⟨i.val, by omega⟩) A)
  have hOver := overhead_lower primitive A n k
  have hOverScale := Nat.mul_le_mul_right (PaperIndexedArrayConstruction.overhead primitive A n k) hc
  rw [PaperIndexedArrayConstruction.fill_work]
  unfold arrayFootprint
  rw [GeneralPaperIndexedArrayLifetime.prefix_data]
  simp only [FixedArrayTable.read_ofFn]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id, ← Finset.mul_sum] at hSum ⊢
  nlinarith only [hSum, hOver, hOverScale]

theorem every_prefix_charged {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (A c : ℕ)
    (callback : Fin n → α × ℕ) (encode : α → ℕ) (hc : 16 ≤ c)
    (h : ∀ j, encode (callback j).1 ≤ c * (callback j).2) (k : ℕ) (hk : k ≤ n) :
    arrayFootprint A encode (prefixTable primitive A callback k hk) ≤
      c * (PaperIndexedArrayConstruction.run primitive A callback).2 :=
  (prefix_charged primitive A c callback encode hc h k hk).trans
    (Nat.mul_le_mul_left c (GeneralPaperIndexedArrayLifetime.fill_work_mono primitive A callback k n hk le_rfl hk))

theorem callback_work_charged {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (A : ℕ)
    (callback : Fin n → α × ℕ) (j : Fin n) :
    (callback j).2 ≤ (PaperIndexedArrayConstruction.run primitive A callback).2 := by
  have h := Finset.single_le_sum (s := Finset.univ) (f := fun i => (callback i).2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [PaperIndexedArrayConstruction.run_work]
  omega

end Blotto.GeneralPaperIndexedArrayAllocationCredit
