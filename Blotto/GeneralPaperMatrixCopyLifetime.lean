import Blotto.GeneralPaperReferenceListCopyLifetime

/-! Nested indexed row copying retains the source matrix at its original
width, destination outer buffers at their target width and the literal
currently active inner row-copy window. Both cursor dimensions are covered. -/
namespace Blotto.GeneralPaperMatrixCopyLifetime
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def window {m r : ℕ} (S A : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ))
    (i : ℕ) (hi : i ≤ r) (j : ℕ) (hj : j ≤ m) : ℕ :=
  GeneralPaperReferenceArrayCopyLifetime.window S A (arrayFootprint S rationalWordWidth)
    (arrayFootprint A rationalWordWidth) (GeneralPaperScalarTableCopy.run S A rationalWordWidth) source
    (fun row => GeneralPaperScalarTableCopyLifetime.window S A rationalWordWidth (source.read row) j hj) i hi

def profile (S A m r P : ℕ) : ℕ :=
  GeneralPaperReferenceArrayCopyLifetime.profile S A (arrayProfile S r (arrayProfile S m P))
    (r * arrayProfile A m P) (arrayProfile A m P) r (GeneralPaperScalarTableCopy.price S A m (m * P))
    (GeneralPaperScalarTableCopyLifetime.profile S A m (m * P) P)

theorem all_cursors {m r : ℕ} (S A P : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ))
    (h : ∀ i j,rationalWordWidth ((source.read i).read j) ≤ P)
    (hA : 1 ≤ A) (hIndexM : binaryWordWidth (m + 1) ≤ A) (hIndexR : binaryWordWidth (r + 1) ≤ A)
    (i : ℕ) (hi : i ≤ r) (j : ℕ) (hj : j ≤ m) :
    window S A source i hi j hj ≤ profile S A m r P := by
  have hRows : ∀ row,arrayFootprint S rationalWordWidth (source.read row) ≤ arrayProfile S m P :=
    fun row => array_bound S P rationalWordWidth (source.read row) (h row)
  have hTarget : ∀ row,arrayFootprint A rationalWordWidth
      (GeneralPaperScalarTableCopy.run S A rationalWordWidth (source.read row)).1 ≤ arrayProfile A m P := by
    intro row
    rw [GeneralPaperScalarTableCopy.data]
    exact array_bound A P rationalWordWidth (source.read row) (h row)
  have hB := Finset.sum_le_sum (s := Finset.univ) (fun row _ => hTarget row)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hB
  have hPayload : ∀ row,(∑ col : Fin m,rationalWordWidth ((source.read row).read col)) ≤ m * P := by
    intro row
    have hSum := Finset.sum_le_sum (s := Finset.univ) (fun col _ => h row col)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hSum
  exact GeneralPaperReferenceArrayCopyLifetime.all_cursors S A _ _ _ _ _
    (arrayFootprint S rationalWordWidth) (arrayFootprint A rationalWordWidth)
    (GeneralPaperScalarTableCopy.run S A rationalWordWidth) source
    (fun row => GeneralPaperScalarTableCopyLifetime.window S A rationalWordWidth (source.read row) j hj)
    (array_bound S _ _ source hRows) hB hTarget
    (fun row => GeneralPaperScalarTableCopy.bounded_work S A P rationalWordWidth (source.read row) (h row))
    (fun row => GeneralPaperScalarTableCopyLifetime.all_cursors S A (m * P) P rationalWordWidth
      (source.read row) (hPayload row) (h row) hA hIndexM j hj) hA hIndexR i hi

theorem source_data {m r : ℕ} (S A : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ)) :
    (PaperIndexedArrayConstruction.run id A
      (GeneralPaperReferenceArrayCopyLifetime.callback S
        (GeneralPaperScalarTableCopy.run S A rationalWordWidth) source)).1 =
      (GeneralPaperScalarTableCopy.matrix S A source).1 := rfl

theorem source_work {m r : ℕ} (S A : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ)) :
    (GeneralPaperScalarTableCopy.matrix S A source).2 =
      (PaperIndexedArrayConstruction.run id A
        (GeneralPaperReferenceArrayCopyLifetime.callback S
          (GeneralPaperScalarTableCopy.run S A rationalWordWidth) source)).2 + 64 * (S + A + 1) := rfl

end Blotto.GeneralPaperMatrixCopyLifetime
