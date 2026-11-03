import Blotto.GeneralPaperEqualBitPreparationLedger

/-! Every retained prefix of the executed indexed-array builder, with loop
activation frames. The paper mutable-reference-array interpretation retains
one prefix buffer; callbacks supply their own separate live scratch bound.
No claim about Lean persistent arrays or the host allocator is made. -/
namespace Blotto.GeneralPaperIndexedArrayLifetime
open scoped BigOperators
open GeneralPaperEncodedBasisStorage (arrayFootprint arrayProfile array_bound)
open GeneralPaperEncodedScalarStorage (fields fields_bound natBits)
set_option autoImplicit false
set_option maxHeartbeats 1400000

def prefixTable {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (A : ℕ)
    (callback : Fin n → α × ℕ) (k : ℕ) (hk : k ≤ n) : FixedArrayTable k α :=
  ⟨(PaperIndexedArrayConstruction.fill primitive A callback k hk).1,
    (by rw [PaperIndexedArrayConstruction.fill_data, Array.size_ofFn])⟩

theorem prefix_data {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (A : ℕ)
    (callback : Fin n → α × ℕ) (k : ℕ) (hk : k ≤ n) :
    prefixTable primitive A callback k hk =
      FixedArrayTable.ofFn (fun j : Fin k => (callback ⟨j.val, by omega⟩).1) := by
  unfold prefixTable FixedArrayTable.ofFn
  congr 1
  exact PaperIndexedArrayConstruction.fill_data primitive A callback k hk

theorem prefix_payload {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (A : ℕ)
    (callback : Fin n → α × ℕ) (encode : α → ℕ) (P : ℕ)
    (hP : ∀ j, encode (callback j).1 ≤ P) (k : ℕ) (hk : k ≤ n) :
    arrayFootprint A encode (prefixTable primitive A callback k hk) ≤ arrayProfile A n P := by
  have h := array_bound A P encode (prefixTable primitive A callback k hk) (by
    intro j
    rw [prefix_data, FixedArrayTable.read_ofFn]
    exact hP _)
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (A + P) hk) (64 * A))

theorem fill_work_mono {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (A : ℕ)
    (callback : Fin n → α × ℕ) (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) (hij : i ≤ j) :
    (PaperIndexedArrayConstruction.fill primitive A callback i hi).2 ≤
      (PaperIndexedArrayConstruction.fill primitive A callback j hj).2 := by
  induction j generalizing i with
  | zero =>
    have he : i = 0 := by omega
    subst i
    exact le_rfl
  | succ j ih =>
    by_cases he : i = j + 1
    · subst i; exact le_rfl
    · have h := ih i hi (by omega) (by omega)
      rw [PaperIndexedArrayConstruction.fill]
      dsimp only
      omega

def frameFoot (A n index counter : ℕ) : ℕ := fields A [n, index, counter] + 32 * A

def frame (A n F : ℕ) : ℕ := 3 * (natBits (n + F + 1) + A) + 64 * A

theorem frame_mono (A n F G : ℕ) (h : F ≤ G) : frame A n F ≤ frame A n G := by
  have hw := Nat.add_le_add_left (binaryWordWidth_mono (show n + F + 1 ≤ n + G + 1 by omega)) 1
  unfold frame natBits
  omega

theorem frame_bound (A n F index counter : ℕ) (hi : index ≤ n) (hc : counter ≤ F) :
    frameFoot A n index counter ≤ frame A n F := by
  have h := fields_bound A (natBits (n + F + 1)) [n, index, counter] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega)
  change fields A [n, index, counter] ≤ 3 * (natBits (n + F + 1) + A) + 32 * A at h
  unfold frameFoot frame
  omega

def activationFoot {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (A : ℕ)
    (callback : Fin n → α × ℕ) (k : ℕ) (hk : k ≤ n) : ℕ :=
  ∑ j : Fin (n - k + 1), frameFoot A n (k + j.val)
    (PaperIndexedArrayConstruction.fill primitive A callback k hk).2

theorem activation_bound {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (A : ℕ)
    (callback : Fin n → α × ℕ) (k : ℕ) (hk : k ≤ n) :
    activationFoot primitive A callback k hk ≤
      (n + 1) * frame A n (PaperIndexedArrayConstruction.run primitive A callback).2 := by
  have hWork := fill_work_mono primitive A callback k n hk le_rfl hk
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin (n - k + 1)) _ =>
    frame_bound A n (PaperIndexedArrayConstruction.run primitive A callback).2
      (k + j.val) (PaperIndexedArrayConstruction.fill primitive A callback k hk).2 (by omega) hWork)
  change activationFoot primitive A callback k hk ≤ _ at hSum
  have h := Nat.mul_le_mul_right (frame A n (PaperIndexedArrayConstruction.run primitive A callback).2)
    (show n - k + 1 ≤ n + 1 by omega)
  exact hSum.trans (by simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using h)

def window {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (A : ℕ)
    (callback : Fin n → α × ℕ) (encode : α → ℕ) (k : ℕ) (hk : k ≤ n)
    (borrowed scratch : ℕ) : ℕ :=
  borrowed + arrayFootprint A encode (prefixTable primitive A callback k hk) + activationFoot primitive A callback k hk + scratch

theorem window_bound {α : Type*} {n : ℕ} (primitive : ℕ → ℕ) (A : ℕ)
    (callback : Fin n → α × ℕ) (encode : α → ℕ) (P S : ℕ)
    (hP : ∀ j, encode (callback j).1 ≤ P) (k : ℕ) (hk : k ≤ n)
    (borrowed scratch : ℕ) (hS : scratch ≤ S) :
    window primitive A callback encode k hk borrowed scratch ≤
      borrowed + arrayProfile A n P +
        (n + 1) * frame A n (PaperIndexedArrayConstruction.run primitive A callback).2 + S := by
  have hPrefix := prefix_payload primitive A callback encode P hP k hk
  have hFrames := activation_bound primitive A callback k hk
  unfold window
  omega

end Blotto.GeneralPaperIndexedArrayLifetime
