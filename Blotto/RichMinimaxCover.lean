import Blotto.RichSecurityAttainment
import Blotto.FiniteMixturePayoff
import Blotto.FinitePayoffSeparation

/-! Actual finite regular-rich response covers and their separating mixtures.
Compactness ranges over all supported poor whole laws; finite mixing preserves
rich regularity. No uniform smoothing or supplied minimax comparator is used. -/

namespace Blotto.RichMinimaxCover
open MeasureTheory Set Filter
open RichSmoothingLaw RichSmoothingApproximation CompactFeasibleLaws ContinuousSecurityValues
open scoped Topology BigOperators Classical

theorem exists_finite_regular_cover {n : ℕ} (values : Values n) {A B : ℝ}
    (hB : 0 < B) (hn : 2 ≤ n) (hBudgets : B < A) (threshold : ℝ)
    (hThreshold : threshold < lossInfimum values B A) :
    ∃ k : ℕ, ∃ laws : Fin k → Mixed n, (∀ i, Regular A (laws i)) ∧
      ∀ opponent : Mixed n, Supported B opponent →
        ∃ i, threshold < expected values (laws i) opponent := by
  let Index := {smooth : Mixed n // Regular A smooth}
  let cover : Index → Set (Mixed n) := fun smooth =>
    {opponent | threshold < expected values smooth.val opponent}
  have hOpen : ∀ smooth, IsOpen (cover smooth) := fun smooth =>
    isOpen_lt continuous_const (regular_rich_expected_continuous values smooth.val smooth.property)
  have hCover : {opponent : Mixed n | Supported B opponent} ⊆ ⋃ smooth, cover smooth := by
    intro opponent hOpponent
    have hSecurity := lossInfimum_le_of_supported values B A (hB.trans hBudgets).le opponent hOpponent
    have hBetter : threshold < security values A opponent := hThreshold.trans_le hSecurity
    obtain ⟨smooth,hRegular,hPayoff⟩ := exists_regular_near_security values (hB.trans hBudgets)
      hn hBudgets opponent hOpponent (security values A opponent - threshold) (by linarith)
    apply mem_iUnion.mpr
    refine ⟨⟨smooth,hRegular⟩,?_⟩
    change threshold < expected values smooth opponent
    linarith
  obtain ⟨chosen,hChosen⟩ := (supported_compact B).elim_finite_subcover cover hOpen hCover
  let selected : Fin (Fintype.card chosen) → Index := fun i =>
    ((Fintype.equivFin chosen).symm i).val
  let laws : Fin (Fintype.card chosen) → Mixed n := fun i => (selected i).val
  refine ⟨Fintype.card chosen,laws,(fun i => (selected i).property),?_⟩
  intro opponent hOpponent
  obtain ⟨smooth,hMember,hPayoff⟩ := by
    simpa only [mem_iUnion] using hChosen hOpponent
  let label : chosen := ⟨smooth,hMember⟩
  refine ⟨(Fintype.equivFin chosen) label,?_⟩
  change threshold < expected values
    (((Fintype.equivFin chosen).symm ((Fintype.equivFin chosen) label)).val.val) opponent
  rw [Equiv.symm_apply_apply]
  exact hPayoff

noncomputable def payoffMap {n k : ℕ} (values : Values n) (laws : Fin k → Mixed n)
    (opponent : Mixed n) : Fin k → ℝ := fun i => expected values (laws i) opponent

theorem payoffMap_continuous {n k : ℕ} (values : Values n) {A : ℝ}
    (laws : Fin k → Mixed n) (hRegular : ∀ i, Regular A (laws i)) :
    Continuous (payoffMap values laws) := by
  apply continuous_pi
  intro i
  exact regular_rich_expected_continuous values (laws i) (hRegular i)

theorem payoffImage_convex {n k : ℕ} (values : Values n) (B : ℝ) (laws : Fin k → Mixed n) :
    Convex ℝ (payoffMap values laws '' {opponent : Mixed n | Supported B opponent}) := by
  rintro x ⟨first,hFirst,rfl⟩ y ⟨second,hSecond,rfl⟩ a b ha hb hSum
  let weights : Fin 2 → ℝ := ![a,b]
  let opponents : Fin 2 → Mixed n := ![first,second]
  have hWeights : ∀ i, 0 ≤ weights i := by intro i; fin_cases i <;> assumption
  have hWeightsSum : ∑ i, weights i = 1 := by simpa [weights,Fin.sum_univ_two] using hSum
  let mixed := probabilityMixture weights opponents hWeights hWeightsSum
  have hMixed : Supported B mixed := probabilityMixture_supported B weights opponents
    hWeights hWeightsSum (by intro i; fin_cases i <;> assumption)
  refine ⟨mixed,hMixed,?_⟩
  ext i
  change expected values (laws i) mixed = a * expected values (laws i) first + b * expected values (laws i) second
  rw [expected_probabilityMixture_right]
  simp [weights,opponents,Fin.sum_univ_two]

/-- The finite cover, actual convex compact payoff image and normalized
separator yield one regular whole law exceeding the threshold against every
canonical supported poor law. This is the retained R33 separation step. -/
theorem exists_regular_uniform_response {n : ℕ} (values : Values n) {A B : ℝ}
    (hB : 0 < B) (hn : 2 ≤ n) (hBudgets : B < A) (threshold : ℝ)
    (hThreshold : threshold < lossInfimum values B A) :
    ∃ smooth : Mixed n, Regular A smooth ∧
      ∀ opponent : Mixed n, Supported B opponent → threshold < expected values smooth opponent := by
  obtain ⟨k,laws,hRegular,hCover⟩ := exists_finite_regular_cover values hB hn hBudgets threshold hThreshold
  let image := payoffMap values laws '' {opponent : Mixed n | Supported B opponent}
  have hNonempty : image.Nonempty := by
    refine ⟨payoffMap values laws (PureBoundaryEquilibria.pointLaw (fun _ => 0)),?_⟩
    exact ⟨_,PureBoundaryEquilibria.pointLaw_supported B _ (feasible_zero hB.le),rfl⟩
  have hCompact : IsCompact image := (supported_compact B).image (payoffMap_continuous values laws hRegular)
  have hDisjoint : Disjoint (FinitePayoffSeparation.lowerOrthant threshold) image := by
    apply Set.disjoint_left.mpr
    rintro row hLower ⟨opponent,hOpponent,rfl⟩
    obtain ⟨i,hBetter⟩ := hCover opponent hOpponent
    exact (hLower i).not_gt hBetter
  obtain ⟨weights,hWeights,hSum,hSecured⟩ := FinitePayoffSeparation.exists_probability_separator
    image hNonempty (payoffImage_convex values B laws) hCompact threshold hDisjoint
  refine ⟨probabilityMixture weights laws hWeights hSum,
    regular_mixture A weights laws hWeights hSum hRegular,?_⟩
  intro opponent hOpponent
  rw [expected_probabilityMixture_left]
  exact hSecured (payoffMap values laws opponent) ⟨opponent,hOpponent,rfl⟩

end Blotto.RichMinimaxCover
