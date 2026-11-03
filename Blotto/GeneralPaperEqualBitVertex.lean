import Blotto.GeneralPaperEqualBitBoundaryScan

/-! A dominant row stores the original budget once and zero in every other
coordinate. The bit price is additive in budget precision, with one reference
array write per field; the original budget is not charged n times. -/
namespace Blotto.GeneralPaperEqualBitVertex
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000

def run {n : ℕ} (A : ℕ) (budget : ℚ) (chosen : Fin n) : RationalResourceArray n × ℕ :=
  let actual := PaperIndexedArrayConstruction.run id A (fun j : Fin n =>
    let q := if j = chosen then budget else 0
    (q, rationalWordWidth q + 32 * A + 32))
  (⟨actual.1.data, actual.1.size⟩, actual.2 + 64 * A + 64)

theorem data {n : ℕ} (A : ℕ) (budget : ℚ) (chosen : Fin n) :
    (run A budget chosen).1.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen := by
  funext j
  change (((PaperIndexedArrayConstruction.run id A (fun j : Fin n =>
    let q := if j = chosen then budget else 0
    (q, rationalWordWidth q + 32 * A + 32))).1.read j : ℚ) : ℝ) = _
  rw [PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn]
  by_cases h : j = chosen <;> simp only [PureBoundaryEquilibria.vertex, h, ite_true, ite_false, Rat.cast_zero]

theorem payload {n : ℕ} (budget : ℚ) (chosen : Fin n) :
    (∑ j : Fin n, rationalWordWidth (if j = chosen then budget else 0)) ≤ 3 * n + rationalWordWidth budget := by
  have hZero : rationalWordWidth (0 : ℚ) = 3 := by decide
  have hEach (j : Fin n) : rationalWordWidth (if j = chosen then budget else 0) ≤
      3 + (if j = chosen then rationalWordWidth budget else 0) := by
    by_cases h : j = chosen
    · simp only [h, ite_true]; omega
    · simp only [h, ite_false, hZero]; omega
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hEach j)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  nlinarith only [h]

def bound (A n b : ℕ) : ℕ := b + 3 * n + n * (32 * A + 32) +
  PaperIndexedArrayConstruction.overhead id A n n + 64 * A + 64

theorem work {n : ℕ} (A : ℕ) (budget : ℚ) (chosen : Fin n) :
    (run A budget chosen).2 ≤ bound A n (rationalWordWidth budget) := by
  have hp := payload budget chosen
  unfold run bound
  dsimp only
  rw [PaperIndexedArrayConstruction.run_work]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id]
  nlinarith only [hp]

theorem encoded_payload {n : ℕ} (A : ℕ) (budget : ℚ) (chosen : Fin n) :
    (∑ j : Fin n, rationalWordWidth ((run A budget chosen).1.allocation j)) ≤ 3 * n + rationalWordWidth budget := by
  have h : (run A budget chosen).1.allocation = fun j => if j = chosen then budget else 0 := by
    funext j
    change (PaperIndexedArrayConstruction.run id A (fun j : Fin n =>
      let q := if j = chosen then budget else 0
      (q, rationalWordWidth q + 32 * A + 32))).1.read j = _
    rw [PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn]
  rw [h]
  exact payload budget chosen

end Blotto.GeneralPaperEqualBitVertex
