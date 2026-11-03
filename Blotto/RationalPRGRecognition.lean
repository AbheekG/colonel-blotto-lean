import Blotto.RationalPRGOriginalInput

/-! Computable checking of the ordered original PRG input contract.
Success constructs the certified input from the supplied rational data;
rejection means a canonical input/promise test failed, not Nash nonexistence. -/

namespace Blotto
open scoped BigOperators

def RationalPRGChecks {n : ℕ} (values : Fin n → ℚ) (a b : ℚ) : Prop :=
  (∀ j, 0 < values j) ∧ (∑ j, values j) = 1 ∧ 0 < a ∧ 0 < b ∧ b ≤ a ∧ ∀ j, 2 * a * values j ≤ b

def rationalPRGChecksBool {n : ℕ} (values : Fin n → ℚ) (a b : ℚ) : Bool :=
  let row := List.ofFn values
  row.all (fun q => decide (0 < q)) && decide (row.sum = 1) && decide (0 < a) &&
    decide (0 < b) && decide (b ≤ a) && row.all (fun q => decide (2 * a * q ≤ b))

theorem rationalPRGChecksBool_iff {n : ℕ} (values : Fin n → ℚ) (a b : ℚ) :
    rationalPRGChecksBool values a b = true ↔ RationalPRGChecks values a b := by
  simp [rationalPRGChecksBool, RationalPRGChecks, List.sum_ofFn, List.mem_ofFn, and_assoc]

def rationalPRGChecksDecidable {n : ℕ} (values : Fin n → ℚ) (a b : ℚ) : Decidable (RationalPRGChecks values a b) := by
  if h : rationalPRGChecksBool values a b = true then
    exact isTrue ((rationalPRGChecksBool_iff values a b).mp h)
  else
    exact isFalse (fun hChecks => h ((rationalPRGChecksBool_iff values a b).mpr hChecks))

def checkRationalPRG {n : ℕ} (values : Fin n → ℚ) (a b : ℚ) : Option (RationalPRGOriginalInput n) :=
  letI := rationalPRGChecksDecidable values a b
  if h : RationalPRGChecks values a b then
    some ⟨values, h.1, h.2.1, a, b, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  else none

theorem checkRationalPRG_isSome {n : ℕ} (values : Fin n → ℚ) (a b : ℚ) :
    (checkRationalPRG values a b).isSome = true ↔ RationalPRGChecks values a b := by
  unfold checkRationalPRG
  split <;> simp_all

theorem checkRationalPRG_none {n : ℕ} (values : Fin n → ℚ) (a b : ℚ) :
    checkRationalPRG values a b = none ↔ ¬RationalPRGChecks values a b := by
  unfold checkRationalPRG
  split <;> simp_all

theorem checkRationalPRG_data {n : ℕ} (values : Fin n → ℚ) (a b : ℚ) (i : RationalPRGOriginalInput n)
    (h : checkRationalPRG values a b = some i) : i.values = values ∧ i.a = a ∧ i.b = b := by
  unfold checkRationalPRG at h
  split at h
  · cases Option.some.inj h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

theorem checkRationalPRG_complete {n : ℕ} (i : RationalPRGOriginalInput n) :
    checkRationalPRG i.values i.a i.b = some i := by
  have h : RationalPRGChecks i.values i.a i.b :=
    ⟨i.positive, i.normalized, i.a_pos, i.b_pos, i.b_le, i.small_fields⟩
  unfold checkRationalPRG
  rw [dite_eq_left h]

end Blotto
