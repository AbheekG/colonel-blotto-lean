import Blotto.RationalRawGroupRouting
import Blotto.RationalTerminalGroupInputs

/-! The low-dimensional sampler reads the prepared group-total array.
Numerical fields equal the retained specifications; proof fields are erased. -/

namespace Blotto
open scoped BigOperators

namespace RationalUniformGroupSpec

theorem eq_of_fields {m : ℕ} (s t : RationalUniformGroupSpec m) (hB : s.B = t.B) (hL : s.length = t.length) : s = t := by
  cases s
  cases t
  cases hB
  cases hL
  rfl

end RationalUniformGroupSpec
namespace RationalMixedGroupSpec

theorem eq_of_fields {m : ℕ} (s t : RationalMixedGroupSpec m) (hB : s.B = t.B) (hL : s.length = t.length)
    (hEll : s.ell = t.ell) (hP : s.p = t.p) : s = t := by
  cases s
  cases t
  cases hB
  cases hL
  cases hEll
  cases hP
  rfl

end RationalMixedGroupSpec
namespace RationalTerminalPacking

def uniformSpec {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (h : ∀ j, ¬(0 < i.resource j ∧ i.resource j < i.length j)) : RationalUniformGroupSpec i.groups.length where
  B := i.B
  length := (fun g => (p.groups.read g).2)
  B_pos := i.B_pos
  length_pos := by intro g; rw [p.total_correct]; exact i.partition.total_pos g
  length_le := by intro g; rw [p.total_correct]; exact i.partition_total_le g
  balance := by
    have hEq : (fun g => (p.groups.read g).2) = i.partition.total := funext p.total_correct
    rw [hEq]
    exact (i.uniformSpec h).balance

theorem uniformSpec_eq {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (h : ∀ j, ¬(0 < i.resource j ∧ i.resource j < i.length j)) : p.uniformSpec h = i.uniformSpec h := by
  exact RationalUniformGroupSpec.eq_of_fields (p.uniformSpec h) (i.uniformSpec h) rfl (funext p.total_correct)

def mixedSpec {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (pivot : Fin n) (hp : 0 < i.resource pivot ∧ i.resource pivot < i.length pivot) : RationalMixedGroupSpec i.groups.length where
  B := i.B
  length := (fun g => (p.groups.read g).2)
  ell := i.length pivot
  p := i.resource pivot / i.length pivot
  B_pos := i.B_pos
  length_pos := by intro g; rw [p.total_correct]; exact i.partition.total_pos g
  length_le := by intro g; rw [p.total_correct]; exact i.partition_total_le g
  ell_pos := i.length_pos pivot
  ell_le := i.length_le pivot
  p_pos := div_pos hp.1 (i.length_pos pivot)
  p_lt := (div_lt_one (i.length_pos pivot)).mpr hp.2
  balance := by
    have hEq : (fun g => (p.groups.read g).2) = i.partition.total := funext p.total_correct
    rw [hEq]
    exact (i.mixedSpec pivot hp).balance

theorem mixedSpec_eq {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (pivot : Fin n) (hp : 0 < i.resource pivot ∧ i.resource pivot < i.length pivot) : p.mixedSpec pivot hp = i.mixedSpec pivot hp := by
  exact RationalMixedGroupSpec.eq_of_fields (p.mixedSpec pivot hp) (i.mixedSpec pivot hp)
    rfl (funext p.total_correct) rfl rfl

end RationalTerminalPacking
end Blotto
