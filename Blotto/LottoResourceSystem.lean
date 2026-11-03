import Blotto.TerminalLottoLaw
import Blotto.ActiveResourceRounding

/-! Global coupling of zero/uniform marginals. Resource rounding supplies
terminal vectors; the greedy grouped terminal laws supply whole allocations.
This is mathematical lottery semantics, not yet the maintained-array sampler
or a computational complexity theorem. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators

structure LottoResourceSystem (n : ℕ) where
  B : ℝ
  length : Allocation n
  initial : Allocation n
  B_pos : 0 < B
  length_pos : ∀ j, 0 < length j
  length_le : ∀ j, length j ≤ B
  initial_box : InBox length initial
  initial_sum : (∑ j, initial j) = 2 * B

namespace LottoResourceSystem

def Valid {n : ℕ} (i : LottoResourceSystem n) (r : Allocation n) : Prop :=
  InBox i.length r ∧ (∑ j, r j) = 2 * i.B ∧ (fractionalSet i.length r).card ≤ 1

noncomputable def terminal {n : ℕ} (i : LottoResourceSystem n) (r : Allocation n)
    (hr : i.Valid r) : TerminalLotto n :=
  ⟨i.B, i.length, r, i.B_pos, i.length_pos, i.length_le, hr.1, hr.2.1, hr.2.2⟩

noncomputable def leafLaw {n : ℕ} (i : LottoResourceSystem n) (r : Allocation n) : Mixed n := by
  classical
  exact if hr : i.Valid r then (i.terminal r hr).law else segmentLaw 0 0

noncomputable def tree {n : ℕ} (i : LottoResourceSystem n) : RoundingTree n :=
  activeResourceTree i.length i.initial

theorem tree_valid {n : ℕ} (i : LottoResourceSystem n) : i.tree.ForLeaves i.Valid := by
  have hc := (activeResourceTree_contract i.length i.initial i.initial_box).2.2
  exact i.tree.forLeaves_mono (fun r hr => ⟨hr.1, hr.2.1.trans i.initial_sum, hr.2.2⟩) hc

theorem tree_height {n : ℕ} (i : LottoResourceSystem n) : i.tree.height ≤ n - 1 :=
  (activeResourceTree_contract i.length i.initial i.initial_box).1

theorem tree_average {n : ℕ} (i : LottoResourceSystem n) : i.tree.average = i.initial :=
  (activeResourceTree_contract i.length i.initial i.initial_box).2.1

noncomputable def law {n : ℕ} (i : LottoResourceSystem n) : Mixed n := i.tree.eval i.leafLaw

theorem leafLaw_contract {n : ℕ} (i : LottoResourceSystem n) (r : Allocation n) (hr : i.Valid r) :
    (∀ᵐ x ∂(i.leafLaw r : Measure (Allocation n)), FullBudget i.B x) ∧
      ∀ j, (marginal (i.leafLaw r) j : Measure ℝ) = affineMeasure (r j / i.length j)
        (uniformLaw (i.length j)) (Measure.dirac 0) := by
  classical
  rw [leafLaw, dite_eq_left hr]
  exact (i.terminal r hr).law_contract

theorem law_contract {n : ℕ} (i : LottoResourceSystem n) :
    (∀ᵐ x ∂(i.law : Measure (Allocation n)), FullBudget i.B x) ∧
      ∀ j, (marginal i.law j : Measure ℝ) = affineMeasure (i.initial j / i.length j)
        (uniformLaw (i.length j)) (Measure.dirac 0) := by
  constructor
  · apply i.tree.eval_fullBudget
    exact i.tree.forLeaves_mono (fun r hr => (i.leafLaw_contract r hr).1) i.tree_valid
  · intro j
    have hbox := i.tree.forLeaves_mono (fun _ hr => hr.1) i.tree_valid
    have hm := i.tree.forLeaves_mono (fun r hr => (i.leafLaw_contract r hr).2 j) i.tree_valid
    have he := i.tree.eval_affine_marginal i.leafLaw i.length i.length_pos j j
      (uniformLaw (i.length j)) (Measure.dirac 0) hbox hm
    simpa only [i.tree_average, law] using he

theorem law_supported {n : ℕ} (i : LottoResourceSystem n) : Supported i.B i.law :=
  i.law_contract.1.mono (fun _ hx => ⟨hx.1, le_of_eq hx.2⟩)

theorem law_zeroUniform {n : ℕ} (i : LottoResourceSystem n) (j : Fin n) :
    (marginal i.law j : Measure ℝ) = zeroUniformLaw (i.length j) (i.initial j / i.length j) := by
  rw [i.law_contract.2 j]
  exact add_comm _ _

end LottoResourceSystem
end Blotto
