import Blotto.GeneralPaperScalarTableCopyLifetime

/-! Every cursor of the pure selected row's actual copy at its stored draw
reference. The index-width premise is derived from that reference formula;
source and returned buffer payloads retain the original budget only once. -/
namespace Blotto.GeneralPaperEqualPureCopyLifetime
open GeneralPaperEncodedScalarStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem address_index (n m k b : ℕ) :
    binaryWordWidth (n + 1) ≤ GeneralPaperEqualBitDrawRates.address n m k b := by
  unfold GeneralPaperEqualBitDrawRates.address StoredArrayReferenceList.poolAddressWidth
  apply binaryWordWidth_mono
  have h := Nat.mul_le_mul_left (n + m + k + 69)
    (show 1 ≤ GeneralPaperEqualBitDrawRates.word n k b + 1 by omega)
  nlinarith only [h]

def table {n : ℕ} (source : RationalResourceArray n) : FixedArrayTable n ℚ := ⟨source.data,source.size⟩

def window {n : ℕ} (S A : ℕ) (source : RationalResourceArray n) (j : ℕ) (hj : j ≤ n) : ℕ :=
  GeneralPaperScalarTableCopyLifetime.window S A rationalWordWidth (table source) j hj

def profile (S n k b : ℕ) : ℕ :=
  GeneralPaperScalarTableCopyLifetime.profile S (GeneralPaperEqualBitDrawRates.address n 0 k b + 1)
    n (3 * n + b) (b + 3)

theorem all_cursors {n : ℕ} (S k : ℕ) (budget : ℚ) (chosen : Fin n) (source : RationalResourceArray n)
    (correct : source.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (j : ℕ) (hj : j ≤ n) :
    window S (GeneralPaperEqualBitDrawRates.address n 0 k (rationalWordWidth budget) + 1) source j hj ≤
      profile S n k (rationalWordWidth budget) := by
  have hB : (∑ i : Fin n,rationalWordWidth ((table source).read i)) ≤ 3 * n + rationalWordWidth budget := by
    change (∑ i : Fin n,rationalWordWidth (source.allocation i)) ≤ _
    simp_rw [GeneralPaperEqualBitCanonical.pure_coordinates budget chosen source correct]
    exact GeneralPaperEqualBitVertex.payload budget chosen
  have hP : ∀ i : Fin n,rationalWordWidth ((table source).read i) ≤ rationalWordWidth budget + 3 := by
    intro i
    change rationalWordWidth (source.allocation i) ≤ _
    rw [GeneralPaperEqualBitCanonical.pure_coordinates budget chosen source correct]
    have hZero : rationalWordWidth (0 : ℚ) = 3 := by decide
    split_ifs <;> omega
  exact GeneralPaperScalarTableCopyLifetime.all_cursors S _ _ _ rationalWordWidth (table source) hB hP
    (by omega) ((address_index n 0 k (rationalWordWidth budget)).trans (by omega)) j hj

theorem source_data {n : ℕ} (S A : ℕ) (source : RationalResourceArray n) :
    (GeneralPaperScalarTableCopy.run S A rationalWordWidth (table source)).1.data =
      (GeneralPaperEqualSelectedCopy.row S A source).1.data := rfl

theorem source_work {n : ℕ} (S A : ℕ) (source : RationalResourceArray n) :
    (GeneralPaperEqualSelectedCopy.row S A source).2 =
      (GeneralPaperScalarTableCopy.run S A rationalWordWidth (table source)).2 + 64 * (S + A + 1) := rfl

end Blotto.GeneralPaperEqualPureCopyLifetime
