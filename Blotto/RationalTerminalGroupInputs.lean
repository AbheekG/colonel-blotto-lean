import Blotto.RationalTerminalLotto
import Blotto.RationalGroupSpecs
import Blotto.RationalResourceContracts

/-! Native terminal resource states compile the exact group-input promises,
with no supplied partition and no real-to-rational recovery. -/

namespace Blotto
open scoped BigOperators

namespace RationalTerminalLotto

def ofActive {n : ℕ} (B : ℚ) (L : Fin n → ℚ) (hB : 0 < B) (hL : ∀ j, 0 < L j)
    (hLB : ∀ j, L j ≤ B) (s : RationalActiveResources L)
    (hs : RationalResourceInvariant L (2 * (B : ℝ)) s) (ht : s.active.length ≤ 1) : RationalTerminalLotto n where
  B := B
  length := L
  resource := s.resource.allocation
  B_pos := hB
  length_pos := hL
  length_le := hLB
  box := fun j => by
    have hb := hs.1 j
    change (0 : ℝ) ≤ (s.resource.allocation j : ℝ) ∧ (s.resource.allocation j : ℝ) ≤ (L j : ℝ) at hb
    exact_mod_cast hb
  resource_sum := by
    have he := hs.2
    change (∑ j, (s.resource.allocation j : ℝ)) = 2 * (B : ℝ) at he
    exact_mod_cast he
  fractional_le := by
    have he := s.realView.length_eq_card
    change s.active.length = (fractionalSet (fun j => (L j : ℝ)) (fun j => (s.resource.allocation j : ℝ))).card at he
    omega

def uniformSpec {n : ℕ} (i : RationalTerminalLotto n)
    (h : ∀ j, ¬(0 < i.resource j ∧ i.resource j < i.length j)) : RationalUniformGroupSpec i.groups.length where
  B := i.B
  length := i.partition.total
  B_pos := i.B_pos
  length_pos := i.partition.total_pos
  length_le := i.partition_total_le
  balance := i.partition_mass.trans (i.uniformMass_no_fraction h)

def mixedSpec {n : ℕ} (i : RationalTerminalLotto n) (pivot : Fin n)
    (hp : 0 < i.resource pivot ∧ i.resource pivot < i.length pivot) : RationalMixedGroupSpec i.groups.length where
  B := i.B
  length := i.partition.total
  ell := i.length pivot
  p := i.resource pivot / i.length pivot
  B_pos := i.B_pos
  length_pos := i.partition.total_pos
  length_le := i.partition_total_le
  ell_pos := i.length_pos pivot
  ell_le := i.length_le pivot
  p_pos := div_pos hp.1 (i.length_pos pivot)
  p_lt := (div_lt_one (i.length_pos pivot)).mpr hp.2
  balance := by
    rw [i.partition_mass, div_mul_cancel₀ _ (ne_of_gt (i.length_pos pivot))]
    exact i.uniformMass_with_fraction pivot hp

theorem fractional_not_in_groups {n : ℕ} (i : RationalTerminalLotto n) (pivot : Fin n)
    (hp : 0 < i.resource pivot ∧ i.resource pivot < i.length pivot) : ∀ g, pivot ∉ i.partition.members g := by
  intro g hg
  have he := (i.partition_covers pivot).mp ⟨g, hg⟩
  exact ne_of_lt hp.2 he

end RationalTerminalLotto
end Blotto
