import Blotto.RationalTerminalGroupInputs
import Blotto.PreparedGroupLaw

/-! Exact reference law for the native terminal partition and native pivot.
Its prescribed marginals follow directly; no equality with another selector's
whole terminal law is required. -/

namespace Blotto.RationalTerminalLotto
open MeasureTheory

theorem endpoint_resource {n : ℕ} (i : RationalTerminalLotto n) (j : Fin n)
    (hj : ¬(0 < i.resource j ∧ i.resource j < i.length j)) : i.resource j = 0 ∨ i.resource j = i.length j := by
  have h := i.real.endpoint_resource j (fun hf => hj ((i.fractional_iff j).mp hf))
  change (i.resource j : ℝ) = 0 ∨ (i.resource j : ℝ) = (i.length j : ℝ) at h
  exact_mod_cast h

theorem partition_real_covers {n : ℕ} (i : RationalTerminalLotto n) (j : Fin n) :
    (∃ g, j ∈ i.partition.real.members g) ↔ i.resource j = i.length j := by
  simpa only [RationalProportionalGroups.real, List.mem_toFinset] using i.partition_covers j

noncomputable def exactUniformLaw {n : ℕ} (i : RationalTerminalLotto n)
    (h : ∀ j, ¬(0 < i.resource j ∧ i.resource j < i.length j)) : Mixed n :=
  i.partition.real.splitLaw ((i.uniformSpec h).real.law i.groups_count)

noncomputable def exactMixedLaw {n : ℕ} (i : RationalTerminalLotto n) (pivot : Fin n)
    (hp : 0 < i.resource pivot ∧ i.resource pivot < i.length pivot) : Mixed n :=
  i.partition.real.splitMixedLaw pivot ((i.mixedSpec pivot hp).real.law i.groups_count)

theorem exactUniformLaw_contract {n : ℕ} (i : RationalTerminalLotto n)
    (h : ∀ j, ¬(0 < i.resource j ∧ i.resource j < i.length j)) :
    (∀ᵐ x ∂(i.exactUniformLaw h : Measure (Allocation n)), FullBudget (i.B : ℝ) x) ∧
      ∀ j, (marginal (i.exactUniformLaw h) j : Measure ℝ) =
        affineMeasure ((i.resource j : ℝ) / (i.length j : ℝ)) (uniformLaw (i.length j : ℝ)) (Measure.dirac 0) := by
  have hc := (i.uniformSpec h).real.law_contract i.groups_count
  have hu : ∀ g, (marginal ((i.uniformSpec h).real.law i.groups_count) g : Measure ℝ) = uniformLaw (i.partition.real.total g) := by
    intro g
    rw [← i.partition.total_real]
    exact hc.2 g
  refine ⟨i.partition.real.splitLaw_fullBudget _ hc.1, ?_⟩
  intro j
  by_cases hj : i.resource j = i.length j
  · rcases (i.partition_real_covers j).mpr hj with ⟨g, hg⟩
    have hm := i.partition.real.splitLaw_uniform _ hu hg
    change (marginal (i.exactUniformLaw h) j : Measure ℝ) = uniformLaw (i.length j : ℝ) at hm
    rw [hm, hj, div_self (by exact_mod_cast ne_of_gt (i.length_pos j))]
    simp [affineMeasure]
  · have hz : i.resource j = 0 := (i.endpoint_resource j (h j)).resolve_right hj
    have hn : ∀ g, j ∉ i.partition.real.members g := fun g hg => hj ((i.partition_real_covers j).mp ⟨g, hg⟩)
    have hm := i.partition.real.splitLaw_inactive ((i.uniformSpec h).real.law i.groups_count) hn
    change (marginal (i.exactUniformLaw h) j : Measure ℝ) = Measure.dirac 0 at hm
    rw [hm, hz]
    simp [affineMeasure]

theorem exactMixedLaw_contract {n : ℕ} (i : RationalTerminalLotto n) (pivot : Fin n)
    (hp : 0 < i.resource pivot ∧ i.resource pivot < i.length pivot) :
    (∀ᵐ x ∂(i.exactMixedLaw pivot hp : Measure (Allocation n)), FullBudget (i.B : ℝ) x) ∧
      ∀ j, (marginal (i.exactMixedLaw pivot hp) j : Measure ℝ) =
        affineMeasure ((i.resource j : ℝ) / (i.length j : ℝ)) (uniformLaw (i.length j : ℝ)) (Measure.dirac 0) := by
  have hc := (i.mixedSpec pivot hp).real.law_contract i.groups_count
  have hpn : ∀ g, pivot ∉ i.partition.real.members g := by
    simpa only [RationalProportionalGroups.real, List.mem_toFinset] using i.fractional_not_in_groups pivot hp
  have hu : ∀ g, (marginal ((i.mixedSpec pivot hp).real.law i.groups_count) g.castSucc : Measure ℝ) =
      uniformLaw (i.partition.real.total g) := by
    intro g
    rw [← i.partition.total_real]
    exact hc.2.1 g
  refine ⟨i.partition.real.splitMixedLaw_fullBudget pivot _ hc.1, ?_⟩
  intro j
  by_cases hjp : j = pivot
  · subst j
    change (marginal (i.partition.real.splitMixedLaw pivot _) pivot : Measure ℝ) = _
    rw [i.partition.real.splitMixedLaw_pivot pivot hpn, hc.2.2]
    change zeroUniformLaw (i.length pivot : ℝ) ((i.resource pivot / i.length pivot : ℚ) : ℝ) = _
    rw [Rat.cast_div]
    exact add_comm _ _
  · by_cases hj : i.resource j = i.length j
    · rcases (i.partition_real_covers j).mpr hj with ⟨g, hg⟩
      have hm := i.partition.real.splitMixedLaw_uniform pivot hpn _ hu hg
      change (marginal (i.exactMixedLaw pivot hp) j : Measure ℝ) = uniformLaw (i.length j : ℝ) at hm
      rw [hm, hj, div_self (by exact_mod_cast ne_of_gt (i.length_pos j))]
      simp [affineMeasure]
    · have hf : ¬(0 < i.resource j ∧ i.resource j < i.length j) := fun hj => hjp (i.fractional_unique hj hp)
      have hz : i.resource j = 0 := (i.endpoint_resource j hf).resolve_right hj
      have hn : ∀ g, j ∉ i.partition.real.members g := fun g hg => hj ((i.partition_real_covers j).mp ⟨g, hg⟩)
      have hm := i.partition.real.splitMixedLaw_inactive pivot ((i.mixedSpec pivot hp).real.law i.groups_count) hn hjp
      change (marginal (i.exactMixedLaw pivot hp) j : Measure ℝ) = Measure.dirac 0 at hm
      rw [hm, hz]
      simp [affineMeasure]

noncomputable def exactLaw {n : ℕ} (i : RationalTerminalLotto n) : Mixed n :=
  match h : i.pivot with
  | none => i.exactUniformLaw (i.pivot_none h)
  | some pivot => i.exactMixedLaw pivot (i.pivot_some h)

theorem exactLaw_contract {n : ℕ} (i : RationalTerminalLotto n) :
    (∀ᵐ x ∂(i.exactLaw : Measure (Allocation n)), FullBudget (i.B : ℝ) x) ∧
      ∀ j, (marginal i.exactLaw j : Measure ℝ) =
        affineMeasure ((i.resource j : ℝ) / (i.length j : ℝ)) (uniformLaw (i.length j : ℝ)) (Measure.dirac 0) := by
  unfold exactLaw
  split
  · exact i.exactUniformLaw_contract _
  · exact i.exactMixedLaw_contract _ _

end Blotto.RationalTerminalLotto
