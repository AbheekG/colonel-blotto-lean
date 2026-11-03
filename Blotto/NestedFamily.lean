import Blotto.NestedFirst
import Blotto.NestedResidual
import Blotto.BinaryMixture

/-! The fixed-mean nested family F_x and valid inputs to the first-case
construction at new interval lengths. -/

namespace Blotto.NestedInput
open MeasureTheory Set

noncomputable def familyProbability (i : NestedInput) (x : ℝ) : ℝ := i.h / (i.c - x)

noncomputable def familyLaw (i : NestedInput) (x : ℝ) : Measure ℝ :=
  ENNReal.ofReal (i.familyProbability x) • uniformLaw x +
    ENNReal.ofReal (1 - i.familyProbability x) • uniformLaw i.c

theorem fixed_mean_identity (i : NestedInput) : i.a + i.d + i.c - i.h = 2 * i.M := by
  dsimp [h]
  nlinarith [i.balance]

theorem familyProbability_bounds (i : NestedInput) {x : ℝ} (hx : x < i.u + i.v) :
    0 < i.familyProbability x ∧ i.familyProbability x < 1 := by
  have hxc : x < i.c := lt_trans hx i.lengths.2.2.2.2
  have hd : 0 < i.c - x := sub_pos.mpr hxc
  constructor
  · exact div_pos i.h_pos hd
  · apply (div_lt_one hd).mpr
    linarith [i.transformed_balance]

/-- Replace t by x while preserving the first two lengths, budget, and mean. -/
noncomputable def atLength (i : NestedInput) (x : ℝ) (hx0 : 0 < x) (hx : x < i.u + i.v) : NestedInput where
  M := i.M
  a := i.a
  d := i.d
  c := i.c
  t := x
  q := i.familyProbability x
  a_pos := i.a_pos
  d_pos := i.d_pos
  c_pos := i.c_pos
  t_pos := hx0
  t_lt := lt_trans hx i.lengths.2.2.2.2
  q_pos := (i.familyProbability_bounds hx).1
  q_lt := (i.familyProbability_bounds hx).2
  a_le := i.a_le
  d_le := i.d_le
  c_le := i.c_le
  ordered := i.ordered
  balance := by
    have hd : i.c - x ≠ 0 := ne_of_gt (sub_pos.mpr (lt_trans hx i.lengths.2.2.2.2))
    have he := congrArg (fun y : ℝ => y * (i.c - x)) i.fixed_mean_identity
    dsimp [familyProbability]
    field_simp [hd]
    nlinarith

theorem atLength_parameters (i : NestedInput) (x : ℝ) (hx0 : 0 < x) (hx : x < i.u + i.v) :
    (i.atLength x hx0 hx).u = i.u ∧ (i.atLength x hx0 hx).v = i.v ∧
      (i.atLength x hx0 hx).h = i.h ∧ (i.atLength x hx0 hx).nestedTargetLaw = i.familyLaw x := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  change i.h / (i.c - x) * (i.c - x) = i.h
  exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr (lt_trans hx i.lengths.2.2.2.2)))

theorem familyLaw_original (i : NestedInput) : i.familyLaw i.t = i.nestedTargetLaw := by
  have hp : i.familyProbability i.t = i.q := by
    dsimp [familyProbability, h]
    field_simp [ne_of_gt (sub_pos.mpr i.t_lt)]
  rw [familyLaw, hp]
  rfl

/-- Exact raw-interval density representation, with positive global divisors. -/
theorem familyLaw_density (i : NestedInput) {x : ℝ} (hx0 : 0 < x) (hx : x < i.u + i.v) :
    i.familyLaw x =
      ENNReal.ofReal (i.familyProbability x / x) • rawInterval 0 x +
        ENNReal.ofReal ((1 - i.familyProbability x) / i.c) • rawInterval 0 i.c := by
  have hp := i.familyProbability_bounds hx
  rw [familyLaw, uniformLaw_density hx0, uniformLaw_density i.c_pos, smul_smul, smul_smul,
    ← ENNReal.ofReal_mul (le_of_lt hp.1),
    ← ENNReal.ofReal_mul (sub_nonneg.mpr (le_of_lt hp.2))]
  congr 2 <;> congr 1 <;> ring

noncomputable def familyFirstLaw (i : NestedInput) (x : ℝ) (hx0 : 0 < x)
    (hxv : x ≤ i.v) : Mixed 3 :=
  (i.atLength x hx0 (by linarith [i.lengths.2.2.1])).firstLaw hxv

theorem familyFirstLaw_contract (i : NestedInput) (x : ℝ) (hx0 : 0 < x) (hxv : x ≤ i.v) :
    (∀ᵐ y ∂(i.familyFirstLaw x hx0 hxv : Measure (Allocation 3)), FullBudget i.M y) ∧
    (marginal (i.familyFirstLaw x hx0 hxv) 0 : Measure ℝ) = uniformLaw i.a ∧
    (marginal (i.familyFirstLaw x hx0 hxv) 1 : Measure ℝ) = uniformLaw i.d ∧
    (marginal (i.familyFirstLaw x hx0 hxv) 2 : Measure ℝ) = i.familyLaw x := by
  exact (i.atLength x hx0 (by linarith [i.lengths.2.2.1])).first_coupling_contract hxv

noncomputable def familyFirstPoint (i : NestedInput) (x : ℝ) (hx0 : 0 < x)
    (hxv : x ≤ i.v) (r : ℝ) (edge : Fin 9) (t : ℝ) : Allocation 3 :=
  let j := i.atLength x hx0 (by linarith [i.lengths.2.2.1])
  j.firstPoint hxv (j.location r) edge t

theorem familyFirstPoint_fullBudget (i : NestedInput) (x : ℝ) (hx0 : 0 < x)
    (hxv : x ≤ i.v) {r t : ℝ} (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1) (edge : Fin 9) :
    FullBudget i.M (i.familyFirstPoint x hx0 hxv r edge t) :=
  (i.atLength x hx0 (by linarith [i.lengths.2.2.1])).firstSamplePath_fullBudget hxv hr ht edge

end Blotto.NestedInput
