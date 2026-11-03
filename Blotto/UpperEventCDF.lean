import Blotto.RealCDFDistance

/-! Kolmogorov distance controls arbitrary upper events on the real line.
The finite boundary may be included or excluded; empty and full events are
handled separately, so this result applies to laws with atoms. -/

namespace Blotto
open MeasureTheory Set

namespace RealCDFClose

theorem open_upper {ρ σ : ProbabilityMeasure ℝ} {δ : ℝ} (h : RealCDFClose ρ σ δ) (z : ℝ) :
    |(ρ : Measure ℝ).real (Ioi z) - (σ : Measure ℝ).real (Ioi z)| ≤ δ := by
  have he : Ioi z = (Iic z)ᶜ := by ext x; simp
  rw [he, measureReal_compl measurableSet_Iic, measureReal_compl measurableSet_Iic, probReal_univ, probReal_univ]
  have heq : (1 - (ρ : Measure ℝ).real (Iic z)) - (1 - (σ : Measure ℝ).real (Iic z)) =
      (σ : Measure ℝ).real (Iic z) - (ρ : Measure ℝ).real (Iic z) := by ring
  rw [heq, abs_sub_comm]
  exact h z

theorem upper_event {ρ σ : ProbabilityMeasure ℝ} {δ : ℝ} (h : RealCDFClose ρ σ δ)
    (A : Set ℝ) (hup : ∀ x ∈ A, ∀ y, x ≤ y → y ∈ A) :
    |(ρ : Measure ℝ).real A - (σ : Measure ℝ).real A| ≤ δ := by
  classical
  by_cases he : A = ∅
  · subst A
    simpa only [measureReal_empty, sub_self, abs_zero] using h.nonnegative
  by_cases hu : A = univ
  · subst A
    simpa only [probReal_univ, sub_self, abs_zero] using h.nonnegative
  have hn : A.Nonempty := Set.nonempty_iff_ne_empty.mpr he
  have hout : ∃ x, x ∉ A := by
    by_contra hx
    apply hu
    ext x
    simp only [mem_univ, iff_true]
    exact not_not.mp (fun hnx => hx ⟨x, hnx⟩)
  rcases hout with ⟨outside, hout⟩
  have hb : BddBelow A := ⟨outside, by
    intro x hx
    by_contra hnle
    exact hout (hup x hx outside (le_of_lt (lt_of_not_ge hnle)))⟩
  let c := sInf A
  have hc : ∀ x ∈ A, c ≤ x := fun _ hx => csInf_le hb hx
  have habove : ∀ x, c < x → x ∈ A := by
    intro x hx
    rcases (csInf_lt_iff hb hn).mp hx with ⟨y, hy, hyx⟩
    exact hup y hy x (le_of_lt hyx)
  by_cases hca : c ∈ A
  · have hA : A = Ici c := by
      ext x
      exact ⟨hc x, fun hx => hup c hca x hx⟩
    rw [hA]
    exact h.upper c
  · have hA : A = Ioi c := by
      ext x
      constructor
      · intro hx
        exact lt_of_le_of_ne (hc x hx) (fun heq => hca (heq.symm ▸ hx))
      · exact habove x
    rw [hA]
    exact h.open_upper c

end RealCDFClose
end Blotto
