import Blotto.DyadicSegmentLottery

/-! A native rational finite segment descriptor. Its exact real
interpretation is the maintained lottery, and emitted rational coordinates
are the verified dyadic segment path. Component selection is compiled
separately from this descriptor. -/

namespace Blotto
open scoped BigOperators

theorem SegmentLottery.eq_of_fields {n k : ℕ} (l t : SegmentLottery n k)
    (hw : l.weight = t.weight) (hP : l.P = t.P) (hQ : l.Q = t.Q) : l = t := by
  cases l
  cases t
  cases hw
  cases hP
  cases hQ
  rfl

structure RationalSegmentLottery (n k : ℕ) where
  weight : Fin k → ℚ
  P : Fin k → Fin n → ℚ
  Q : Fin k → Fin n → ℚ
  nonnegative : ∀ i, 0 ≤ weight i
  mass : (∑ i, weight i) = 1

namespace RationalSegmentLottery

noncomputable def real {n k : ℕ} (l : RationalSegmentLottery n k) : SegmentLottery n k where
  weight := fun i => l.weight i
  P := fun i j => l.P i j
  Q := fun i j => l.Q i j
  nonnegative := fun i => by exact_mod_cast l.nonnegative i
  mass := by exact_mod_cast l.mass

def point {n k : ℕ} (l : RationalSegmentLottery n k) (K : ℕ) (slot : Fin k) (bits : Fin K → Bool) : Fin n → ℚ :=
  rationalSegmentPoint (l.P slot) (l.Q slot) (dyadicMidpointSample K bits)

theorem point_real {n k : ℕ} (l : RationalSegmentLottery n k) (K : ℕ) (slot : Fin k) (bits : Fin K → Bool) :
    (fun j => (l.point K slot bits j : ℝ)) = l.real.dyadicPoint K slot bits := by
  exact rationalSegmentPoint_real (l.P slot) (l.Q slot) _

theorem point_fullBudget {n k : ℕ} (l : RationalSegmentLottery n k) (K : ℕ) {B : ℝ}
    (h : ∀ slot, FullBudget B (l.real.P slot) ∧ FullBudget B (l.real.Q slot)) (slot : Fin k) (bits : Fin K → Bool) :
    FullBudget B (fun j => (l.point K slot bits j : ℝ)) := by
  rw [l.point_real]
  exact l.real.dyadicPoint_fullBudget K h slot bits

end RationalSegmentLottery
end Blotto
