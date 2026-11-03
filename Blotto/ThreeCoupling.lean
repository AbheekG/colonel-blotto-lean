import Blotto.ThreeMarginals
import Blotto.ThreeInput
import Blotto.Permutation

/-! The normalized three-variable whole-allocation law. This closes the
mathematical coupling, while sampling cost and finite-bit accuracy remain
separate operational obligations. -/

namespace Blotto
open MeasureTheory Set

namespace ThreeGeometry

theorem couplingLaw_marginals (g : ThreeGeometry) :
    (marginal g.couplingLaw 0 : Measure ℝ) = uniformLaw g.a ∧
    (marginal g.couplingLaw 1 : Measure ℝ) = uniformLaw g.d ∧
    (marginal g.couplingLaw 2 : Measure ℝ) = zeroUniformLaw g.c g.mixtureProbability := by
  unfold couplingLaw chosenWeights
  split_ifs with hwv hwu
  · exact ⟨g.first_marginal_x hwv, g.first_marginal_y hwv, g.first_marginal_z hwv⟩
  · exact ⟨g.second_marginal_x hwu, g.second_marginal_y hwu, g.second_marginal_z hwu⟩
  · have huw := le_of_lt (lt_of_not_ge hwu)
    exact ⟨g.third_marginal_x huw, g.third_marginal_y huw, g.third_marginal_z huw⟩

/-- The interpolation used by an actual selected edge. Feasibility is pointwise,
including zero-weight edges and endpoint parameters. -/
noncomputable def couplingPoint (g : ThreeGeometry) (i : Fin 9) (t : ℝ) : Allocation 3 :=
  segmentPoint (g.vertex (threeEdges i).1) (g.vertex (threeEdges i).2) t

theorem couplingPoint_fullBudget (g : ThreeGeometry) (i : Fin 9) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) : FullBudget g.budget (g.couplingPoint i t) :=
  g.every_segment_fullBudget _ _ ht

end ThreeGeometry

namespace ThreeInput

noncomputable def exceptionalLaw (i : ThreeInput) : Mixed 3 :=
  segmentLaw ![0, 0, i.B] ![i.a, i.d, 0]

theorem exceptionalLaw_fullBudget (i : ThreeInput) (he : i.a + i.d - i.B = 0) :
    ∀ᵐ x ∂(i.exceptionalLaw : Measure (Allocation 3)), FullBudget i.B x := by
  apply segmentLaw_fullBudget
  · apply fullBudget_three (le_refl 0) (le_refl 0) (le_of_lt i.B_pos)
    ring
  · apply fullBudget_three (le_of_lt i.a_pos) (le_of_lt i.d_pos) (le_refl 0)
    linarith [i.exceptional_case he]

theorem exceptionalLaw_marginals (i : ThreeInput) (he : i.a + i.d - i.B = 0) :
    (marginal i.exceptionalLaw 0 : Measure ℝ) = uniformLaw i.a ∧
    (marginal i.exceptionalLaw 1 : Measure ℝ) = uniformLaw i.d ∧
    (marginal i.exceptionalLaw 2 : Measure ℝ) = zeroUniformLaw i.c i.p := by
  have hx : ∀ {a : ℝ}, 0 < a → (affineUniform 0 a : Measure ℝ) = uniformLaw a := by
    intro a ha
    rw [affineUniform_increasing ha]
    simp only [intervalLaw, sub_zero, uniformLaw]
  have hec := i.exceptional_case he
  simp [exceptionalLaw, segmentLaw_marginal, hec.1, hec.2.1,
    zeroUniformLaw, hx i.a_pos, hx i.d_pos]
  rw [affineUniform_reverse i.B 0, hx i.B_pos]

noncomputable def couplingLaw (i : ThreeInput) : Mixed 3 :=
  if he : 0 < i.a + i.d - i.B then (i.geometry he).couplingLaw else i.exceptionalLaw

theorem couplingLaw_fullBudget (i : ThreeInput) :
    ∀ᵐ x ∂(i.couplingLaw : Measure (Allocation 3)), FullBudget i.B x := by
  unfold couplingLaw
  split_ifs with he
  · have hg := i.geometry_matches he
    simpa only [hg.2.2.2.1] using (i.geometry he).couplingLaw_fullBudget
  · exact i.exceptionalLaw_fullBudget (le_antisymm (le_of_not_gt he) i.E_nonnegative)

theorem couplingLaw_supported (i : ThreeInput) : Supported i.B i.couplingLaw :=
  i.couplingLaw_fullBudget.mono fun _ hx => ⟨hx.1, le_of_eq hx.2⟩

theorem couplingLaw_marginals (i : ThreeInput) :
    (marginal i.couplingLaw 0 : Measure ℝ) = uniformLaw i.a ∧
    (marginal i.couplingLaw 1 : Measure ℝ) = uniformLaw i.d ∧
    (marginal i.couplingLaw 2 : Measure ℝ) = zeroUniformLaw i.c i.p := by
  unfold couplingLaw
  split_ifs with he
  · have hg := i.geometry_matches he
    simpa only [hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.2] using
      (i.geometry he).couplingLaw_marginals
  · exact i.exceptionalLaw_marginals (le_antisymm (le_of_not_gt he) i.E_nonnegative)

/-- Lemma 2.2 in the a≤d coordinate convention: an actual Borel probability
law exists, with the hard budget and all three prescribed marginal measures. -/
theorem exists_coupling (i : ThreeInput) :
    ∃ μ : Mixed 3, (∀ᵐ x ∂(μ : Measure (Allocation 3)), FullBudget i.B x) ∧
      (marginal μ 0 : Measure ℝ) = uniformLaw i.a ∧
      (marginal μ 1 : Measure ℝ) = uniformLaw i.d ∧
      (marginal μ 2 : Measure ℝ) = zeroUniformLaw i.c i.p :=
  ⟨i.couplingLaw, i.couplingLaw_fullBudget, i.couplingLaw_marginals⟩

end ThreeInput
/-- The mathematical coupling assertion of manuscript Lemma 2.2 with no
ordering restriction on its first two lengths. -/
theorem exists_three_coupling (B a d c p : ℝ)
    (hB : 0 < B) (ha : 0 < a) (hd : 0 < d) (hc : 0 < c) (hp : 0 < p)
    (haB : a ≤ B) (hdB : d ≤ B) (hcB : c ≤ B) (hp1 : p ≤ 1)
    (hbalance : a + d + p * c = 2 * B) :
    ∃ μ : Mixed 3, (∀ᵐ x ∂(μ : Measure (Allocation 3)), FullBudget B x) ∧
      (marginal μ 0 : Measure ℝ) = uniformLaw a ∧
      (marginal μ 1 : Measure ℝ) = uniformLaw d ∧
      (marginal μ 2 : Measure ℝ) = zeroUniformLaw c p := by
  by_cases had : a ≤ d
  · let i : ThreeInput := ⟨B, a, d, c, p, hB, ha, hd, hc, hp, haB, hdB, hcB, hp1, had, hbalance⟩
    exact i.exists_coupling
  · let i : ThreeInput := ⟨B, d, a, c, p, hB, hd, ha, hc, hp, hdB, haB, hcB, hp1,
        le_of_lt (lt_of_not_ge had), by linarith⟩
    rcases i.exists_coupling with ⟨μ, hμ, h0, h1, h2⟩
    refine ⟨swapLaw μ, swapLaw_fullBudget hμ, ?_, ?_, ?_⟩
    · simpa [swapLaw_marginal, swapIndex] using h1
    · simpa [swapLaw_marginal, swapIndex] using h0
    · simpa [swapLaw_marginal, swapIndex] using h2

end Blotto
