import Blotto.GeneralPaperEqualFinalClosureCapacity

/-! The once-only denominator conversion before length-array filling,
including original/converted words, reached copy scratch and parent fields.
Active callbacks and the completed return have existing separate bounds. -/
namespace Blotto.GeneralPaperEqualDenominatorLifetime
open GeneralPaperEncodedScalarStorage (natBits fields)
set_option autoImplicit false
set_option maxHeartbeats 1800000

def window (A n D borrowed : ℕ) : ℕ :=
  let den := GeneralPaperRationalScalarStep.natural A D
  borrowed + GeneralPaperEqualLengthLifetime.denominatorFrame A D + den.2 + fields A [n, A, den.2] + 128 * A

def profile (A n s borrowed : ℕ) : ℕ :=
  borrowed + 256 * (s + A + 1) + 3 * (natBits (n + 128 * (s + A + 1) + 1) + A) + 160 * A

theorem conversion_work (A D s : ℕ) (hs : 2 ≤ s) (hD : binaryWordWidth D ≤ s) :
    (GeneralPaperRationalScalarStep.natural A D).2 ≤ 128 * (s + A + 1) := by
  have hWord := rationalWordWidth_of_height (DyadicMidpointAssembly.nat_height D s (by omega)
    ((lt_pow_binaryWordWidth D).trans_le (Nat.pow_le_pow_right (by decide) hD)))
  unfold GeneralPaperRationalScalarStep.natural
  dsimp only
  omega

theorem bounded (A n D s borrowed : ℕ) (hs : 2 ≤ s) (hD : binaryWordWidth D ≤ s) :
    window A n D borrowed ≤ profile A n s borrowed := by
  have hDen := GeneralPaperEqualLengthLifetime.denominator_bound A D s hs hD
  have hWork := conversion_work A D s hs hD
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (n + 128 * (s + A + 1) + 1)
    [n, A, (GeneralPaperRationalScalarStep.natural A D).2] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 3 * (natBits (n + 128 * (s + A + 1) + 1) + A) + 32 * A at hFields
  simp only [window]
  unfold profile
  omega

theorem borrowed_mono (A n s B C : ℕ) (h : B ≤ C) : profile A n s B ≤ profile A n s C := by unfold profile; omega

@[fun_prop]
theorem profile_scale (n s : ℕ) (borrowed : ℕ → ℕ) (hb : GeneralPaperReferenceScaling.Scale borrowed) :
    GeneralPaperReferenceScaling.Scale (fun A => profile A n s (borrowed A)) := by
  unfold profile
  fun_prop

end Blotto.GeneralPaperEqualDenominatorLifetime
