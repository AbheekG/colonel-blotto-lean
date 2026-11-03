import Blotto.TerminalLottoGrouping
import Blotto.SmallGroupLaws
import Blotto.AffineMixture

/-! Terminal resource vectors give explicit whole-allocation couplings: pack
the saturated coordinates, couple their two or three groups together with the
optional fractional coordinate, and split each group proportionally. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators

namespace TerminalLotto

noncomputable def partition {n : ℕ} (i : TerminalLotto n) : ProportionalGroups n i.groups.length :=
  packingPartition i.length i.length_pos i.B i.uniformItems i.uniformItems_nodup
    (fun j _ => i.length_le j)

theorem partition_covers {n : ℕ} (i : TerminalLotto n) (j : Fin n) :
    (∃ g, j ∈ i.partition.members g) ↔ i.resource j = i.length j := by
  exact (packingPartition_covers i.length i.length_pos i.B i.uniformItems
    i.uniformItems_nodup (fun j _ => i.length_le j) j).trans (i.mem_uniformItems j)

theorem partition_total_le {n : ℕ} (i : TerminalLotto n) (g : Fin i.groups.length) :
    i.partition.total g ≤ i.B := packingPartition_total_bound _ _ _ _ _ _ g

theorem partition_mass {n : ℕ} (i : TerminalLotto n) :
    (∑ g, i.partition.total g) = i.uniformMass := packingPartition_mass _ _ _ _ _ _

theorem groups_count {n : ℕ} (i : TerminalLotto n) : i.groups.length = 2 ∨ i.groups.length = 3 := by
  have hu := i.groups_count_upper
  have hl := i.groups_count_lower
  omega

theorem fractional_not_in_groups {n : ℕ} (i : TerminalLotto n) (pivot : Fin n)
    (hp : Fractional i.length i.resource pivot) : ∀ g, pivot ∉ i.partition.members g := by
  intro g hg
  have he := (i.partition_covers pivot).mp ⟨g, hg⟩
  exact ne_of_lt hp.2 he

noncomputable def uniformSpec {n : ℕ} (i : TerminalLotto n)
    (h : ∀ j, ¬Fractional i.length i.resource j) : UniformGroupSpec i.groups.length where
  B := i.B
  length := i.partition.total
  B_pos := i.B_pos
  length_pos := i.partition.total_pos
  length_le := i.partition_total_le
  balance := i.partition_mass.trans (i.uniformMass_no_fraction h)

noncomputable def uniformLaw {n : ℕ} (i : TerminalLotto n)
    (h : ∀ j, ¬Fractional i.length i.resource j) : Mixed n :=
  i.partition.splitLaw ((i.uniformSpec h).law i.groups_count)

theorem uniformLaw_contract {n : ℕ} (i : TerminalLotto n)
    (h : ∀ j, ¬Fractional i.length i.resource j) :
    (∀ᵐ x ∂(i.uniformLaw h : Measure (Allocation n)), FullBudget i.B x) ∧
      ∀ j, (marginal (i.uniformLaw h) j : Measure ℝ) =
        affineMeasure (i.resource j / i.length j) (Blotto.uniformLaw (i.length j)) (Measure.dirac 0) := by
  have hc := (i.uniformSpec h).law_contract i.groups_count
  refine ⟨i.partition.splitLaw_fullBudget _ hc.1, ?_⟩
  intro j
  by_cases hj : i.resource j = i.length j
  · rcases (i.partition_covers j).mpr hj with ⟨g, hg⟩
    have hm := i.partition.splitLaw_uniform _ hc.2 hg
    change (marginal (i.uniformLaw h) j : Measure ℝ) = Blotto.uniformLaw (i.length j) at hm
    rw [hm, hj, div_self (ne_of_gt (i.length_pos j))]
    simp [affineMeasure]
  · have hz : i.resource j = 0 := (i.endpoint_resource j (h j)).resolve_right hj
    have hn : ∀ g, j ∉ i.partition.members g := fun g hg => hj ((i.partition_covers j).mp ⟨g, hg⟩)
    have hm := i.partition.splitLaw_inactive ((i.uniformSpec h).law i.groups_count) hn
    change (marginal (i.uniformLaw h) j : Measure ℝ) = Measure.dirac 0 at hm
    rw [hm, hz]
    simp [affineMeasure]

noncomputable def mixedSpec {n : ℕ} (i : TerminalLotto n) (pivot : Fin n)
    (hp : Fractional i.length i.resource pivot) : MixedGroupSpec i.groups.length where
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

noncomputable def mixedLaw {n : ℕ} (i : TerminalLotto n) (pivot : Fin n)
    (hp : Fractional i.length i.resource pivot) : Mixed n :=
  i.partition.splitMixedLaw pivot ((i.mixedSpec pivot hp).law i.groups_count)

theorem mixedLaw_contract {n : ℕ} (i : TerminalLotto n) (pivot : Fin n)
    (hp : Fractional i.length i.resource pivot) :
    (∀ᵐ x ∂(i.mixedLaw pivot hp : Measure (Allocation n)), FullBudget i.B x) ∧
      ∀ j, (marginal (i.mixedLaw pivot hp) j : Measure ℝ) =
        affineMeasure (i.resource j / i.length j) (Blotto.uniformLaw (i.length j)) (Measure.dirac 0) := by
  have hc := (i.mixedSpec pivot hp).law_contract i.groups_count
  have hpn := i.fractional_not_in_groups pivot hp
  refine ⟨i.partition.splitMixedLaw_fullBudget pivot _ hc.1, ?_⟩
  intro j
  by_cases hjp : j = pivot
  · subst j
    change (marginal (i.partition.splitMixedLaw pivot _) pivot : Measure ℝ) = _
    rw [i.partition.splitMixedLaw_pivot pivot hpn, hc.2.2]
    simp only [mixedSpec, zeroUniformLaw, affineMeasure]
    exact add_comm _ _
  · by_cases hj : i.resource j = i.length j
    · rcases (i.partition_covers j).mpr hj with ⟨g, hg⟩
      have hm := i.partition.splitMixedLaw_uniform pivot hpn _ hc.2.1 hg
      change (marginal (i.mixedLaw pivot hp) j : Measure ℝ) = Blotto.uniformLaw (i.length j) at hm
      rw [hm, hj, div_self (ne_of_gt (i.length_pos j))]
      simp [affineMeasure]
    · have hf : ¬Fractional i.length i.resource j := fun hj => hjp (i.fractional_unique hj hp)
      have hz : i.resource j = 0 := (i.endpoint_resource j hf).resolve_right hj
      have hn : ∀ g, j ∉ i.partition.members g := fun g hg => hj ((i.partition_covers j).mp ⟨g, hg⟩)
      have hm := i.partition.splitMixedLaw_inactive pivot ((i.mixedSpec pivot hp).law i.groups_count) hn hjp
      change (marginal (i.mixedLaw pivot hp) j : Measure ℝ) = Measure.dirac 0 at hm
      rw [hm, hz]
      simp [affineMeasure]

noncomputable def law {n : ℕ} (i : TerminalLotto n) : Mixed n := by
  classical
  by_cases h : (fractionalSet i.length i.resource).Nonempty
  · exact i.mixedLaw h.choose ((mem_fractionalSet _ _ _).mp h.choose_spec)
  · exact i.uniformLaw (fun j hj => h ⟨j, (mem_fractionalSet _ _ _).mpr hj⟩)

theorem law_contract {n : ℕ} (i : TerminalLotto n) :
    (∀ᵐ x ∂(i.law : Measure (Allocation n)), FullBudget i.B x) ∧
      ∀ j, (marginal i.law j : Measure ℝ) =
        affineMeasure (i.resource j / i.length j) (Blotto.uniformLaw (i.length j)) (Measure.dirac 0) := by
  unfold law
  split_ifs with h
  · exact i.mixedLaw_contract _ _
  · exact i.uniformLaw_contract _

end TerminalLotto
end Blotto
