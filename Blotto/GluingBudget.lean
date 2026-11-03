import Blotto.AuxiliaryGluing

/-! Feasibility and exact auxiliary matching of the constructed joint law. -/

namespace Blotto
open MeasureTheory Set Filter
open scoped BigOperators

namespace AuxiliaryGluing

theorem joint_contract {n m k : ℕ} (G : AuxiliaryGluing n m k) {A B : ℝ}
    (hP : ∀ i, FullBudget A (G.first.P i)) (hQ : ∀ i, FullBudget A (G.first.Q i))
    (hB : ∀ᵐ y ∂(G.second : Measure (Allocation m)), FullBudget B y) :
    ∀ᵐ z ∂G.rawLaw, FullBudget A z.1 ∧ FullBudget B z.2 ∧
      G.firstProbe.value z.1 = G.secondProbe.value z.2 := by
  have hp : MeasurableSet {z : Allocation n × Allocation m |
      FullBudget A z.1 ∧ FullBudget B z.2 ∧ G.firstProbe.value z.1 = G.secondProbe.value z.2} :=
    ((measurable_fullBudget A).preimage measurable_fst).inter
      (((measurable_fullBudget B).preimage measurable_snd).inter
        (measurableSet_eq_fun (G.firstProbe.measurable.comp measurable_fst)
          (G.secondProbe.measurable.comp measurable_snd)))
  unfold rawLaw
  apply Measure.ae_sum_iff.mpr
  intro i
  by_cases h0 : G.first.weight i = 0
  · simp [SegmentLottery.conditionalWeight, h0]
  · have hnonconst : G.firstProbe.value (G.first.P i) ≠ G.firstProbe.value (G.first.Q i) :=
      fun h => h0 (G.first.constant_probe_weight_zero G.firstProbe G.d G.first_uniform i h)
    apply Measure.ae_smul_measure
    rw [ae_map_iff (G.measurable_pairedPoint i).aemeasurable hp]
    have hcell : ∀ᵐ y ∂(G.second : Measure (Allocation m)).restrict (G.cell i), y ∈ G.cell i :=
      ae_restrict_mem (G.measurable_cell i)
    have hBF : ∀ᵐ y ∂(G.second : Measure (Allocation m)).restrict (G.cell i), FullBudget B y :=
      ae_restrict_of_ae hB
    apply (hcell.and hBF).mono
    intro y hy
    exact ⟨G.first.pointAt_fullBudget G.firstProbe hP hQ i hnonconst hy.1,
      hy.2, G.first.pointAt_probe G.firstProbe i hnonconst _⟩

end AuxiliaryGluing

noncomputable def glueAllocation (z : Allocation 3 × Allocation 3) : Allocation 4 :=
  ![z.1 0, z.1 1, z.2 1, z.2 2]

theorem measurable_glueAllocation : Measurable glueAllocation := by
  apply Measurable.of_eval
  intro j
  fin_cases j <;> simp [glueAllocation] <;> fun_prop

theorem glueAllocation_fullBudget {A B d : ℝ} {x y : Allocation 3}
    (hx : FullBudget A x) (hy : FullBudget B y) (hmatch : x 2 = d - y 0) :
    FullBudget (A + B - d) (glueAllocation (x, y)) := by
  constructor
  · intro j
    fin_cases j
    · exact hx.1 0
    · exact hx.1 1
    · exact hy.1 1
    · exact hy.1 2
  · have hA := hx.2
    have hB := hy.2
    simp [Fin.sum_univ_succ] at hA hB
    simp [glueAllocation, Fin.sum_univ_succ]
    linarith

noncomputable def AuxiliaryGluing.allocationLaw {k : ℕ} (G : AuxiliaryGluing 3 3 k) : Mixed 4 :=
  G.jointLaw.map glueAllocation

theorem AuxiliaryGluing.allocationLaw_fullBudget {k : ℕ} (G : AuxiliaryGluing 3 3 k) {A B : ℝ}
    (hP : ∀ i, FullBudget A (G.first.P i)) (hQ : ∀ i, FullBudget A (G.first.Q i))
    (hB : ∀ᵐ y ∂(G.second : Measure (Allocation 3)), FullBudget B y)
    (hF : G.firstProbe = AffineProbe.coordinate (2 : Fin 3))
    (hS : G.secondProbe = AffineProbe.reflectedCoordinate G.d (0 : Fin 3)) :
    ∀ᵐ x ∂(G.allocationLaw : Measure (Allocation 4)), FullBudget (A + B - G.d) x := by
  change ∀ᵐ x ∂Measure.map glueAllocation G.rawLaw, FullBudget (A + B - G.d) x
  rw [ae_map_iff measurable_glueAllocation.aemeasurable (measurable_fullBudget (A + B - G.d))]
  apply (G.joint_contract hP hQ hB).mono
  intro z hz
  have hm := hz.2.2
  rw [hF, hS] at hm
  exact glueAllocation_fullBudget hz.1 hz.2.1 hm

/-- Both first-source and second-source coordinates retain their actual laws. -/
theorem AuxiliaryGluing.allocationLaw_marginals {k : ℕ} (G : AuxiliaryGluing 3 3 k) :
    (marginal G.allocationLaw 0 : Measure ℝ) = (marginal G.first.law 0 : Measure ℝ) ∧
    (marginal G.allocationLaw 1 : Measure ℝ) = (marginal G.first.law 1 : Measure ℝ) ∧
    (marginal G.allocationLaw 2 : Measure ℝ) = (marginal G.second 1 : Measure ℝ) ∧
    (marginal G.allocationLaw 3 : Measure ℝ) = (marginal G.second 2 : Measure ℝ) := by
  have he : ∀ j : Fin 4, (marginal G.allocationLaw j : Measure ℝ) =
      Measure.map (fun z => glueAllocation z j) G.rawLaw := by
    intro j
    change Measure.map (fun x : Allocation 4 => x j) (Measure.map glueAllocation G.rawLaw) = _
    rw [Measure.map_map (measurable_pi_apply j) measurable_glueAllocation]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [he]
    change Measure.map ((fun x : Allocation 3 => x 0) ∘ Prod.fst) G.rawLaw = _
    rw [← Measure.map_map (measurable_pi_apply 0) measurable_fst, G.rawLaw_fst]
    rfl
  · rw [he]
    change Measure.map ((fun x : Allocation 3 => x 1) ∘ Prod.fst) G.rawLaw = _
    rw [← Measure.map_map (measurable_pi_apply 1) measurable_fst, G.rawLaw_fst]
    rfl
  · rw [he]
    change Measure.map ((fun x : Allocation 3 => x 1) ∘ Prod.snd) G.rawLaw = _
    rw [← Measure.map_map (measurable_pi_apply 1) measurable_snd, G.rawLaw_snd]
    rfl
  · rw [he]
    change Measure.map ((fun x : Allocation 3 => x 2) ∘ Prod.snd) G.rawLaw = _
    rw [← Measure.map_map (measurable_pi_apply 2) measurable_snd, G.rawLaw_snd]
    rfl

end Blotto
