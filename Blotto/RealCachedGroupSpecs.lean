import Blotto.RealRawGroupRouting

/-! The low-dimensional sampler reads the prepared group-total array.
Numerical fields equal the retained specifications; proof fields are erased. -/

namespace Blotto
open scoped BigOperators

namespace UniformGroupSpec

theorem eq_of_fields {m : ℕ} (s t : UniformGroupSpec m) (hB : s.B = t.B) (hL : s.length = t.length) : s = t := by
  cases s
  cases t
  cases hB
  cases hL
  rfl

end UniformGroupSpec
namespace MixedGroupSpec

theorem eq_of_fields {m : ℕ} (s t : MixedGroupSpec m) (hB : s.B = t.B) (hL : s.length = t.length)
    (hEll : s.ell = t.ell) (hP : s.p = t.p) : s = t := by
  cases s
  cases t
  cases hB
  cases hL
  cases hEll
  cases hP
  rfl

end MixedGroupSpec
namespace RealPreparedGroupOutput

noncomputable def uniformSpec {n : ℕ} {i : TerminalLotto n} (p : RealPreparedGroupOutput i.partition)
    (h : ∀ j, ¬Fractional i.length i.resource j) : UniformGroupSpec i.groups.length where
  B := i.B
  length := p.totals.read
  B_pos := i.B_pos
  length_pos := by intro g; rw [p.total_correct]; exact i.partition.total_pos g
  length_le := by intro g; rw [p.total_correct]; exact i.partition_total_le g
  balance := by
    have hEq : p.totals.read = i.partition.total := funext p.total_correct
    rw [hEq]
    exact (i.uniformSpec h).balance

theorem uniformSpec_eq {n : ℕ} {i : TerminalLotto n} (p : RealPreparedGroupOutput i.partition)
    (h : ∀ j, ¬Fractional i.length i.resource j) : p.uniformSpec h = i.uniformSpec h := by
  exact UniformGroupSpec.eq_of_fields (p.uniformSpec h) (i.uniformSpec h) rfl (funext p.total_correct)

noncomputable def mixedSpec {n : ℕ} {i : TerminalLotto n} (p : RealPreparedGroupOutput i.partition)
    (pivot : Fin n) (hp : Fractional i.length i.resource pivot) : MixedGroupSpec i.groups.length where
  B := i.B
  length := p.totals.read
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
    have hEq : p.totals.read = i.partition.total := funext p.total_correct
    rw [hEq]
    exact (i.mixedSpec pivot hp).balance

theorem mixedSpec_eq {n : ℕ} {i : TerminalLotto n} (p : RealPreparedGroupOutput i.partition)
    (pivot : Fin n) (hp : Fractional i.length i.resource pivot) : p.mixedSpec pivot hp = i.mixedSpec pivot hp := by
  exact MixedGroupSpec.eq_of_fields (p.mixedSpec pivot hp) (i.mixedSpec pivot hp)
    rfl (funext p.total_correct) rfl rfl

end RealPreparedGroupOutput
end Blotto
