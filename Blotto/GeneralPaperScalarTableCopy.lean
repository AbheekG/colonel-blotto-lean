import Blotto.GeneralPaperEqualBooleanCopy

/-! Scalar table/matrix copies sum payload precision before charging
reference operations. In particular one large entry is not charged once
per table coordinate. Nested matrices copy rows and outer references. -/
namespace Blotto.GeneralPaperScalarTableCopy
open GeneralPaperEncodedBasisStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def run {α : Type*} {n : ℕ} (S A : ℕ) (encode : α → ℕ) (source : FixedArrayTable n α) :=
  GeneralPaperReferenceCopy.array S A (GeneralPaperReferenceCopy.scalar S A encode) source

theorem data {α : Type*} {n : ℕ} (S A : ℕ) (encode : α → ℕ) (source : FixedArrayTable n α) :
    (run S A encode source).1 = source := GeneralPaperReferenceCopy.array_data S A _ (fun _ => rfl) source

def price (S A n P : ℕ) : ℕ := P + n * (32 * (S + A + 1)) + n * (32 * S + 32) +
  (n + 1) * (6 * A + 10 * binaryWordWidth (n + 1) + 28) + 64 * (S + A + 1)

theorem work {α : Type*} {n : ℕ} (S A P : ℕ) (encode : α → ℕ) (source : FixedArrayTable n α)
    (h : (∑ j : Fin n,encode (source.read j)) ≤ P) : (run S A encode source).2 ≤ price S A n P := by
  have ho := PaperIndexedArrayConstruction.overhead_bound id 1 (fun w => by change w ≤ 1 * w; omega) A n n le_rfl
  unfold run
  rw [GeneralPaperReferenceCopy.array_work]
  simp only [GeneralPaperReferenceCopy.scalar,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  unfold price
  nlinarith only [h,ho]

theorem bounded_work {α : Type*} {n : ℕ} (S A P : ℕ) (encode : α → ℕ) (source : FixedArrayTable n α)
    (h : ∀ j,encode (source.read j) ≤ P) : (run S A encode source).2 ≤ price S A n (n * P) := by
  apply work S A (n * P) encode source
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => h j)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hs

theorem charged {α : Type*} {n : ℕ} (S A : ℕ) (encode : α → ℕ) (source : FixedArrayTable n α) :
    arrayFootprint A encode (run S A encode source).1 ≤ 16 * (run S A encode source).2 := by
  apply GeneralPaperReferenceCopy.array_charged S A 16 _ encode source (by decide)
  intro j
  dsimp only [GeneralPaperReferenceCopy.scalar]
  omega

def matrix {m r : ℕ} (S A : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ)) :=
  GeneralPaperReferenceCopy.array S A (run S A rationalWordWidth) source

theorem matrix_data {m r : ℕ} (S A : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ)) :
    (matrix S A source).1 = source := GeneralPaperReferenceCopy.array_data S A _ (data S A rationalWordWidth) source

def matrixPrice (S A m r P : ℕ) : ℕ := GeneralPaperReferenceCopy.arrayPrice S A r (price S A m (m * P))

theorem matrix_work {m r : ℕ} (S A P : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ))
    (h : ∀ i j,rationalWordWidth ((source.read i).read j) ≤ P) :
    (matrix S A source).2 ≤ matrixPrice S A m r P := by
  exact GeneralPaperReferenceCopy.array_bound S A _ _ source (fun i => bounded_work S A P rationalWordWidth (source.read i) (h i))

theorem matrix_charged {m r : ℕ} (S A : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ)) :
    arrayFootprint A (arrayFootprint A rationalWordWidth) (matrix S A source).1 ≤ 16 * (matrix S A source).2 :=
  GeneralPaperReferenceCopy.array_charged S A 16 _ _ source (by decide) (fun i => charged S A rationalWordWidth (source.read i))

end Blotto.GeneralPaperScalarTableCopy
