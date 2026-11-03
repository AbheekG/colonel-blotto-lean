import Blotto.ProportionalGroups
import Blotto.RealCDFDistance

/-! Marginal CDF errors survive proportional group splitting. Whole-allocation
maps are used; no independence between coordinates is introduced. -/

namespace Blotto
open MeasureTheory

namespace RealCDFClose

theorem scale {ρ σ : ProbabilityMeasure ℝ} {δ : ℝ} (h : RealCDFClose ρ σ δ) (c : ℝ) :
    RealCDFClose (ρ.map (fun x => c * x)) (σ.map (fun x => c * x)) δ := by
  have hf : affineLine 0 c = fun x => c * x := by funext x; unfold affineLine; ring
  have he := h.affine 0 c
  rw [hf] at he
  exact he

end RealCDFClose

namespace ProportionalGroups

theorem splitLaw_CDFClose {n m : ℕ} (G : ProportionalGroups n m) (μ ν : Mixed m) {δ : ℝ}
    (hδ : 0 ≤ δ) (hc : CDFClose μ ν δ) : CDFClose (G.splitLaw μ) (G.splitLaw ν) δ := by
  classical
  intro j z
  unfold closedCDF
  by_cases hj : ∃ g, j ∈ G.members g
  · rcases hj with ⟨g, hg⟩
    rw [G.splitLaw_marginal_group μ hg, G.splitLaw_marginal_group ν hg]
    have hs : RealCDFClose (marginal μ g) (marginal ν g) δ := fun t => hc g t
    exact hs.scale (G.length j / G.total g) z
  · have hn : ∀ g, j ∉ G.members g := fun g hg => hj ⟨g, hg⟩
    rw [G.splitLaw_inactive μ hn, G.splitLaw_inactive ν hn]
    simpa only [sub_self, abs_zero] using hδ

theorem splitMixedLaw_marginal_group {n m : ℕ} (G : ProportionalGroups n m) (pivot : Fin n)
    (hp : ∀ g, pivot ∉ G.members g) (μ : Mixed (m + 1)) {i : Fin n} {g : Fin m} (hi : i ∈ G.members g) :
    (marginal (G.splitMixedLaw pivot μ) i : Measure ℝ) =
      Measure.map (fun r => G.length i / G.total g * r) (marginal μ g.castSucc : Measure ℝ) := by
  change Measure.map (fun x : Allocation n => x i)
    (Measure.map (G.splitMixed pivot) (μ : Measure (Allocation (m + 1)))) = _
  rw [Measure.map_map (measurable_pi_apply i) (G.measurable_splitMixed pivot)]
  have he : (fun x : Allocation n => x i) ∘ G.splitMixed pivot =
      (fun r : ℝ => G.length i / G.total g * r) ∘ (fun y : Allocation (m + 1) => y g.castSucc) :=
    funext (G.splitMixed_group pivot hp hi)
  rw [he, ← Measure.map_map (g := fun r : ℝ => G.length i / G.total g * r)
    (measurable_const.mul measurable_id) (measurable_pi_apply g.castSucc)]
  rfl

theorem splitMixedLaw_CDFClose {n m : ℕ} (G : ProportionalGroups n m) (pivot : Fin n)
    (hp : ∀ g, pivot ∉ G.members g) (μ ν : Mixed (m + 1)) {δ : ℝ} (hc : CDFClose μ ν δ) :
    CDFClose (G.splitMixedLaw pivot μ) (G.splitMixedLaw pivot ν) δ := by
  classical
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hc (Fin.last m) 0)
  intro j z
  unfold closedCDF
  by_cases hjp : j = pivot
  · subst j
    rw [G.splitMixedLaw_pivot pivot hp μ, G.splitMixedLaw_pivot pivot hp ν]
    exact hc (Fin.last m) z
  · by_cases hj : ∃ g, j ∈ G.members g
    · rcases hj with ⟨g, hg⟩
      rw [G.splitMixedLaw_marginal_group pivot hp μ hg, G.splitMixedLaw_marginal_group pivot hp ν hg]
      have hs : RealCDFClose (marginal μ g.castSucc) (marginal ν g.castSucc) δ := fun t => hc g.castSucc t
      exact hs.scale (G.length j / G.total g) z
    · have hn : ∀ g, j ∉ G.members g := fun g hg => hj ⟨g, hg⟩
      rw [G.splitMixedLaw_inactive pivot μ hn hjp, G.splitMixedLaw_inactive pivot ν hn hjp]
      simpa only [sub_self, abs_zero] using hδ

end ProportionalGroups
end Blotto
