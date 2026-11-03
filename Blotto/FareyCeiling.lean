import Blotto.FareyPredecessorWork
import Blotto.FareyRationalMembership

/-! The retained direct Farey ceiling primitives, including strict equality
and zero. Strict ceiling reflects strict predecessor. Weak ceiling first checks
the actual reduced denominator and otherwise uses the same reflection. Every
quotient callback is counted by the actual native predecessor observer. -/

namespace Blotto.Farey

def Above (strict : Bool) (threshold bid : ℚ) : Prop := if strict then threshold < bid else threshold ≤ bid

structure CeilingResult (D : ℕ) (threshold : ℚ) (strict : Bool) where
  fraction : Fraction
  bounded : fraction.den ≤ D
  unit : fraction.value ≤ 1
  above : Above strict threshold fraction.value
  least : ∀ other : Fraction, other.den ≤ D → Above strict threshold other.value → fraction.value ≤ other.value

def weakCeiling (D : ℕ) (hD : 0 < D) (threshold : ℚ) : Option (CeilingResult D threshold false) × ℕ :=
  if hZero : threshold ≤ 0 then
    (some ⟨zeroFraction, by change 1 ≤ D; omega, by norm_num [zeroFraction, Fraction.value],
      by simpa [Above, zeroFraction, Fraction.value] using hZero, fun other _ _ => by
        simpa [zeroFraction, Fraction.value] using value_nonnegative other⟩, 0)
  else if hAbove : 1 < threshold then (none, 0)
  else if hMember : threshold.den ≤ D then
    let endpoint := fractionOfRat threshold
    have he : endpoint.value = threshold := fractionOfRat_value threshold (le_of_not_ge hZero)
    (some ⟨endpoint, hMember, by rw [he]; exact le_of_not_gt hAbove,
      by change threshold ≤ endpoint.value; rw [he], fun other _ ho => by
        change threshold ≤ other.value at ho
        rwa [he]⟩, 0)
  else
    have hBelow : threshold < 1 := by
      apply lt_of_le_of_ne (le_of_not_gt hAbove)
      intro h
      have hd : threshold.den = 1 := by rw [h]; norm_num
      rw [hd] at hMember
      omega
    have hCut : 0 < 1 - threshold ∧ 1 - threshold ≤ 1 := by constructor <;> linarith
    let lower := predecessorWithWork D hD (1 - threshold) hCut
    let endpoint := complement lower.result.fraction
    have hLowerUnit : lower.result.fraction.value ≤ 1 := lower.result.strict.le.trans hCut.2
    have he : endpoint.value = 1 - lower.result.fraction.value := complement_value _ hLowerUnit
    have hu : endpoint.value ≤ 1 := complement_unit _ hLowerUnit
    have ha : threshold ≤ endpoint.value := by rw [he]; linarith [lower.result.strict]
    (some ⟨endpoint, lower.result.bounded, hu, ha, fun other hd ho => by
      change threshold ≤ other.value at ho
      by_cases hUnit : other.value ≤ 1
      · have hf := complement_value other hUnit
        have hStrict : (complement other).value < 1 - threshold := by
          rw [hf]
          apply sub_lt_sub_left
          apply lt_of_le_of_ne ho
          intro hEq
          have hDen : threshold.den ≤ D := by rw [hEq]; exact (value_den_le other).trans hd
          exact hMember hDen
        have hg := lower.result.greatest (complement other) hd hStrict
        rw [hf] at hg
        rw [he]
        linarith
      · exact hu.trans (le_of_not_ge hUnit)⟩, lower.quotientQueries)

def strictCeiling (D : ℕ) (hD : 0 < D) (threshold : ℚ) : Option (CeilingResult D threshold true) × ℕ :=
  if hZero : threshold < 0 then
    (some ⟨zeroFraction, by change 1 ≤ D; omega, by norm_num [zeroFraction, Fraction.value],
      by simpa [Above, zeroFraction, Fraction.value] using hZero, fun other _ _ => by
        simpa [zeroFraction, Fraction.value] using value_nonnegative other⟩, 0)
  else if hAbove : 1 ≤ threshold then (none, 0)
  else
    have hCut : 0 < 1 - threshold ∧ 1 - threshold ≤ 1 := by constructor <;> linarith
    let lower := predecessorWithWork D hD (1 - threshold) hCut
    let endpoint := complement lower.result.fraction
    have hLowerUnit : lower.result.fraction.value ≤ 1 := lower.result.strict.le.trans hCut.2
    have he : endpoint.value = 1 - lower.result.fraction.value := complement_value _ hLowerUnit
    have hu : endpoint.value ≤ 1 := complement_unit _ hLowerUnit
    have ha : threshold < endpoint.value := by rw [he]; linarith [lower.result.strict]
    (some ⟨endpoint, lower.result.bounded, hu, ha, fun other hd ho => by
      change threshold < other.value at ho
      by_cases hUnit : other.value ≤ 1
      · have hf := complement_value other hUnit
        have hStrict : (complement other).value < 1 - threshold := by rw [hf]; linarith
        have hg := lower.result.greatest (complement other) hd hStrict
        rw [hf] at hg
        rw [he]
        linarith
      · exact hu.trans (le_of_not_ge hUnit)⟩, lower.quotientQueries)

def ceiling (D : ℕ) (hD : 0 < D) (strict : Bool) (threshold : ℚ) : Option (CeilingResult D threshold strict) × ℕ :=
  match strict with
  | false => weakCeiling D hD threshold
  | true => strictCeiling D hD threshold

theorem weakCeiling_none (D : ℕ) (hD : 0 < D) (threshold : ℚ) :
    (weakCeiling D hD threshold).1 = none ↔ 1 < threshold := by
  unfold weakCeiling
  split_ifs <;> simp_all
  linarith

theorem strictCeiling_none (D : ℕ) (hD : 0 < D) (threshold : ℚ) :
    (strictCeiling D hD threshold).1 = none ↔ 1 ≤ threshold := by
  unfold strictCeiling
  split_ifs <;> simp_all
  linarith

theorem ceiling_none (D : ℕ) (hD : 0 < D) (strict : Bool) (threshold : ℚ) :
    (ceiling D hD strict threshold).1 = none ↔ ¬ Above strict threshold 1 := by
  cases strict
  · simpa [ceiling, Above] using weakCeiling_none D hD threshold
  · simpa [ceiling, Above] using strictCeiling_none D hD threshold

theorem weakCeiling_queries (D : ℕ) (hD : 0 < D) (threshold : ℚ) :
    (weakCeiling D hD threshold).2 ≤ 6 * binaryWordWidth D := by
  unfold weakCeiling
  split_ifs <;> dsimp only
  all_goals try omega
  exact predecessorWithWork_queries D hD _ _

theorem strictCeiling_queries (D : ℕ) (hD : 0 < D) (threshold : ℚ) :
    (strictCeiling D hD threshold).2 ≤ 6 * binaryWordWidth D := by
  unfold strictCeiling
  split_ifs <;> dsimp only
  all_goals try omega
  exact predecessorWithWork_queries D hD _ _

theorem ceiling_queries (D : ℕ) (hD : 0 < D) (strict : Bool) (threshold : ℚ) :
    (ceiling D hD strict threshold).2 ≤ 6 * binaryWordWidth D := by
  cases strict
  · exact weakCeiling_queries D hD threshold
  · exact strictCeiling_queries D hD threshold

theorem above_mono (strict : Bool) (threshold first second : ℚ) (h : first ≤ second)
    (ha : Above strict threshold first) : Above strict threshold second := by
  cases strict
  · exact ha.trans h
  · exact ha.trans_le h

theorem above_translate (strict : Bool) (threshold bid shift : ℚ) :
    Above strict threshold (bid + shift) ↔ Above strict (threshold - shift) bid := by
  cases strict <;> unfold Above <;> dsimp <;> constructor <;> intro h <;> linarith

end Blotto.Farey
