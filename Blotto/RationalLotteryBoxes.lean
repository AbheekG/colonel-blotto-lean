import Blotto.RationalLotterySwap
import Blotto.RationalSegmentFlat
import Blotto.NestedBoxes

/-! Coordinate-box invariants for native descriptor assembly and sampling.
They cover every endpoint and every bit path, including zero-weight slots. -/

namespace Blotto.RationalSegmentLottery

theorem padRight_box {n k : ℕ} (l : RationalSegmentLottery n k) (m : ℕ) (fallback : Fin k)
    (length : Allocation n) (h : ∀ slot, InBox length (l.real.P slot) ∧ InBox length (l.real.Q slot)) :
    ∀ slot, InBox length ((l.padRight m fallback).real.P slot) ∧ InBox length ((l.padRight m fallback).real.Q slot) := by
  intro slot
  refine Fin.addCases ?_ ?_ slot
  · intro j; simpa only [padRight, real, Fin.addCases_left] using h j
  · intro j; simpa only [padRight, real, Fin.addCases_right] using h fallback

theorem binary_box {n k m : ℕ} (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (l : RationalSegmentLottery n k) (t : RationalSegmentLottery n m) (length : Allocation n)
    (hl : ∀ slot, InBox length (l.real.P slot) ∧ InBox length (l.real.Q slot))
    (ht : ∀ slot, InBox length (t.real.P slot) ∧ InBox length (t.real.Q slot)) :
    ∀ slot, InBox length ((binary p hp l t).real.P slot) ∧ InBox length ((binary p hp l t).real.Q slot) := by
  intro slot
  refine Fin.addCases ?_ ?_ slot
  · intro j; simpa only [binary, real, Fin.addCases_left] using hl j
  · intro j; simpa only [binary, real, Fin.addCases_right] using ht j

theorem swapFirst_box {k : ℕ} (l : RationalSegmentLottery 3 k) (a d c : ℝ)
    (h : ∀ slot, InBox ![a, d, c] (l.real.P slot) ∧ InBox ![a, d, c] (l.real.Q slot)) :
    ∀ slot, InBox ![d, a, c] (l.swapFirst.real.P slot) ∧ InBox ![d, a, c] (l.swapFirst.real.Q slot) := by
  rw [l.swapFirst_real]
  intro slot
  constructor
  · intro j
    fin_cases j
    · exact (h slot).1 1
    · exact (h slot).1 0
    · exact (h slot).1 2
  · intro j
    fin_cases j
    · exact (h slot).2 1
    · exact (h slot).2 0
    · exact (h slot).2 2

theorem point_inBox {n k : ℕ} (l : RationalSegmentLottery n k) (K : ℕ) (length : Allocation n)
    (h : ∀ slot, InBox length (l.real.P slot) ∧ InBox length (l.real.Q slot))
    (slot : Fin k) (bits : Fin K → Bool) : InBox length (fun j => (l.point K slot bits j : ℝ)) := by
  rw [l.point_real]
  exact segment_inBox (h slot).1 (h slot).2
    ⟨le_of_lt (dyadicMidpointSample_bounds K bits).1, le_of_lt (dyadicMidpointSample_bounds K bits).2⟩

theorem flatSample_inBox {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (R K : ℕ)
    (length : Allocation n) (h : ∀ slot, InBox length (l.real.P slot) ∧ InBox length (l.real.Q slot))
    (bits : Fin (R + K) → Bool) : InBox length (fun j => (l.flatSample fallback R K bits j : ℝ)) :=
  l.point_inBox K length h _ _

end Blotto.RationalSegmentLottery
