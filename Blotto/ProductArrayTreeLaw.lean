import Blotto.ProductArrayTree

/-! The constructed field-array sampler's exact target is the normalized
constrained product Gibbs law. The label/code bijection preserves duplicate
bids; infeasible Cartesian labels contribute zero before normalization. Full
support sums occur in proofs, not in the recursive sampler implementation. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators Classical
namespace ProductArrayTree

theorem sum_ite_subtype {α : Type*} [Fintype α] (predicate : α → Prop) [DecidablePred predicate]
    (f : α → ℚ) : (∑ x, if predicate x then f x else 0) = ∑ x : {x // predicate x}, f x.val := by
  have h := Fintype.sum_subtype_add_sum_subtype predicate (fun x => if predicate x then f x else 0)
  have hp : (∑ x : {x // predicate x}, if predicate x.val then f x.val else 0) =
      ∑ x : {x // predicate x}, f x.val := by
    apply Finset.sum_congr rfl
    intro x _
    exact ite_eq_left x.property
  have hn : (∑ x : {x // ¬predicate x}, if predicate x.val then f x.val else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact ite_eq_right x.property
  rw [hp, hn, add_zero] at h
  exact h.symm

theorem sum_ite_subtype_real {α : Type*} [Fintype α] (predicate : α → Prop) [DecidablePred predicate]
    (f : α → ℝ) : (∑ x, if predicate x then f x else 0) = ∑ x : {x // predicate x}, f x.val := by
  have h := Fintype.sum_subtype_add_sum_subtype predicate (fun x => if predicate x then f x else 0)
  have hp : (∑ x : {x // predicate x}, if predicate x.val then f x.val else 0) =
      ∑ x : {x // predicate x}, f x.val := by
    apply Finset.sum_congr rfl
    intro x _
    exact ite_eq_left x.property
  have hn : (∑ x : {x // ¬predicate x}, if predicate x.val then f x.val else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact ite_eq_right x.property
  rw [hp, hn, add_zero] at h
  exact h.symm

theorem constructed_prefix_mass (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 ≤ weights j code) (budget : ℚ) :
    (constructed n sizes bids weights hb hw).guideTree.real.trueFamily.prefixMass (budget : ℝ) =
      ((∑ i, SparseMW.feasibleVector bids budget weights i : ℚ) : ℝ) := by
  let tree := constructed n sizes bids weights hb hw
  let eqLabels := finCastEquiv (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize)
  have hTrue : tree.guideTree.real.trueFamily.prefixMass (budget : ℝ) =
      ∑ label : Fin tree.labels, if tree.resource label ≤ budget then (tree.weight label : ℝ) else 0 := by
    unfold WeightedResourceFamily.prefixMass
    rw [← Equiv.sum_comp eqLabels.symm]
    apply Finset.sum_congr rfl
    intro label _
    have hR := tree.resource_eq_trueFamily label
    have hW := tree.weight_eq_trueFamily label
    have hCast : (tree.resource label : ℝ) ≤ (budget : ℝ) ↔ tree.resource label ≤ budget := by norm_cast
    change (if tree.guideTree.real.trueFamily.resource
        (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize).symm) ≤ (budget : ℝ) then
        tree.guideTree.real.trueFamily.mass
          (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize).symm) else 0) = _
    rw [← hR, ← hW]
    simp only [hCast]
  rw [hTrue]
  have hCode : (∑ label : Fin tree.labels, if tree.resource label ≤ budget then tree.weight label else 0) =
      ∑ code : SparseMW.ProductCodes sizes, if SparseMW.productResource bids code ≤ budget then
        SparseMW.productMass weights code else 0 := by
    apply Fintype.sum_equiv (constructedLabelEquiv n sizes bids weights hb hw)
    intro label
    rw [constructed_resource, constructed_weight]
  have hSum : (∑ label : Fin tree.labels, if tree.resource label ≤ budget then tree.weight label else 0) =
      ∑ i, SparseMW.feasibleVector bids budget weights i := by
    rw [hCode, sum_ite_subtype]
    have he := Equiv.sum_comp (SparseMW.feasibleEquiv bids budget)
      (SparseMW.feasibleVector bids budget weights)
    simp only [SparseMW.feasibleVector, Equiv.symm_apply_apply, SparseMW.feasibleMass] at he
    exact he
  have hCast : (∑ label : Fin tree.labels, if tree.resource label ≤ budget then (tree.weight label : ℝ) else 0) =
      ((∑ label : Fin tree.labels, if tree.resource label ≤ budget then tree.weight label else 0 : ℚ) : ℝ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro label _
    split_ifs <;> simp
  rw [hCast, hSum]

theorem constructed_prefix_positive (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 < weights j code) (budget : ℚ)
    (fallback : SparseMW.ProductCodes sizes) (hf : SparseMW.productResource bids fallback ≤ budget) :
    0 < (constructed n sizes bids weights hb (fun j code => (hw j code).le)).guideTree.real.trueFamily.prefixMass (budget : ℝ) := by
  rw [constructed_prefix_mass]
  exact_mod_cast SparseMW.weightSum_positive (SparseMW.feasibleCard_positive bids budget fallback hf)
    _ (SparseMW.feasibleVector_positive bids budget weights hw)

theorem constructed_target_mean (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 < weights j code) (budget : ℚ)
    (fallback : SparseMW.ProductCodes sizes) (hf : SparseMW.productResource bids fallback ≤ budget)
    (f : SparseMW.ProductCodes sizes → ℝ) :
    let hn := fun j code => (hw j code).le
    let tree := constructed n sizes bids weights hb hn
    (tree.guideTree.targetKernel budget (constructed_prefix_positive n sizes bids weights hb hw budget fallback hf)).mean
      (fun label => f (constructedLabelEquiv n sizes bids weights hb hn
        (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize)))) =
      ∑ i, (SparseMW.normalizeQ (SparseMW.feasibleVector bids budget weights) i : ℝ) *
        f (((SparseMW.feasibleEquiv bids budget).symm i).val) := by
  dsimp only
  let hn := fun j code => (hw j code).le
  let tree := constructed n sizes bids weights hb hn
  let denominator := ((∑ i, SparseMW.feasibleVector bids budget weights i : ℚ) : ℝ)
  let eqLabels := finCastEquiv (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize)
  change (∑ label : Fin tree.guideTree.real.trueSize,
    tree.guideTree.real.feasibleTargetWeight (budget : ℝ) label /
      tree.guideTree.real.trueFamily.prefixMass (budget : ℝ) *
      f (constructedLabelEquiv n sizes bids weights hb hn (eqLabels label))) = _
  rw [constructed_prefix_mass]
  rw [← Equiv.sum_comp eqLabels.symm]
  have hNative : (∑ label : Fin tree.labels,
      tree.guideTree.real.feasibleTargetWeight (budget : ℝ) (eqLabels.symm label) / denominator *
        f (constructedLabelEquiv n sizes bids weights hb hn label)) =
      ∑ label : Fin tree.labels, if tree.resource label ≤ budget then
        (tree.weight label : ℝ) / denominator * f (constructedLabelEquiv n sizes bids weights hb hn label) else 0 := by
    apply Finset.sum_congr rfl
    intro label _
    unfold WeightedGuideTree.feasibleTargetWeight
    have hR := tree.resource_eq_trueFamily label
    have hW := tree.weight_eq_trueFamily label
    change (if tree.guideTree.real.trueFamily.resource
        (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize).symm) ≤ (budget : ℝ) then
        tree.guideTree.real.trueFamily.mass
          (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize).symm) else 0) / denominator * _ = _
    rw [← hR, ← hW]
    have hCast : (tree.resource label : ℝ) ≤ (budget : ℝ) ↔ tree.resource label ≤ budget := by norm_cast
    simp only [hCast]
    split_ifs <;> simp
  change (∑ label : Fin tree.labels,
    tree.guideTree.real.feasibleTargetWeight (budget : ℝ) (eqLabels.symm label) / denominator *
      f (constructedLabelEquiv n sizes bids weights hb hn ((eqLabels.symm label).cast
        (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize)))) = _
  have hCast : ∀ label : Fin tree.labels,
      (eqLabels.symm label).cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize) = label :=
    fun _ => Fin.ext rfl
  simp_rw [hCast]
  rw [hNative]
  have hCode : (∑ label : Fin tree.labels, if tree.resource label ≤ budget then
      (tree.weight label : ℝ) / denominator * f (constructedLabelEquiv n sizes bids weights hb hn label) else 0) =
      ∑ code : SparseMW.ProductCodes sizes, if SparseMW.productResource bids code ≤ budget then
        (SparseMW.productMass weights code : ℝ) / denominator * f code else 0 := by
    apply Fintype.sum_equiv (constructedLabelEquiv n sizes bids weights hb hn)
    intro label
    rw [constructed_resource, constructed_weight]
  rw [hCode, sum_ite_subtype_real]
  have hFinite := Equiv.sum_comp (SparseMW.feasibleEquiv bids budget)
    (fun i => (SparseMW.normalizeQ (SparseMW.feasibleVector bids budget weights) i : ℝ) *
      f (((SparseMW.feasibleEquiv bids budget).symm i).val))
  simp only [SparseMW.normalizeQ, SparseMW.feasibleVector, SparseMW.feasibleMass,
    Equiv.symm_apply_apply, Rat.cast_div, Rat.cast_sum] at hFinite
  simpa only [denominator, SparseMW.normalizeQ, SparseMW.feasibleVector, SparseMW.feasibleMass,
    Rat.cast_div, Rat.cast_sum] using hFinite

noncomputable def arrayRow {m : ℕ} {sizes : Fin m → ℕ}
    (bids : (j : Fin m) → Fin (sizes j) → ℚ) (code : SparseMW.ProductCodes sizes) : Allocation m :=
  fun field => (bids field (code field) : ℝ)

theorem constructed_target_row (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 ≤ weights j code)
    (label : Fin (constructed n sizes bids weights hb hw).guideTree.real.trueSize) :
    let tree := constructed n sizes bids weights hb hw
    (fun field : Fin (n + 1) => tree.targetRow label (field.cast (constructed_fields n sizes bids weights hb hw).symm)) =
      arrayRow bids (constructedLabelEquiv n sizes bids weights hb hw
        (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize))) := by
  funext field
  exact congrArg (fun q : ℚ => (q : ℝ)) (constructed_decode n sizes bids weights hb hw
    (label.cast ((constructed n sizes bids weights hb hw).guideTree.real_trueSize.trans
      (constructed n sizes bids weights hb hw).guideTree_trueSize)) field)

theorem constructed_target_row_mean (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 < weights j code) (budget : ℚ)
    (fallback : SparseMW.ProductCodes sizes) (hf : SparseMW.productResource bids fallback ≤ budget)
    (f : Allocation (n + 1) → ℝ) :
    let hn := fun j code => (hw j code).le
    let tree := constructed n sizes bids weights hb hn
    (tree.guideTree.targetKernel budget (constructed_prefix_positive n sizes bids weights hb hw budget fallback hf)).mean
      (fun label => f (fun field => tree.targetRow label
        (field.cast (constructed_fields n sizes bids weights hb hn).symm))) =
      ∑ i, (SparseMW.gibbsWholeRowLaw bids budget fallback hf weights hw).realWeight i *
        f ((SparseMW.gibbsWholeRowLaw bids budget fallback hf weights hw).realRow i) := by
  dsimp only
  have h := constructed_target_mean n sizes bids weights hb hw budget fallback hf (fun code => f (arrayRow bids code))
  simp_rw [constructed_target_row]
  exact h

def sampleRow (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 < weights j code) (budget : ℚ)
    (fallback : SparseMW.ProductCodes sizes) (hf : SparseMW.productResource bids fallback ≤ budget)
    (epsilon : ℚ) (bits : Fin ((constructed n sizes bids weights hb (fun j code => (hw j code).le)).guideTree.epsilonBitBudget epsilon) → Bool) :
    Fin (n + 1) → ℚ :=
  let hn := fun j code => (hw j code).le
  let tree := constructed n sizes bids weights hb hn
  let label := (constructedLabelEquiv n sizes bids weights hb hn).symm fallback
  let sampled := tree.epsilonRow (constructed_certified n sizes bids weights hb hn) budget
    (constructed_prefix_positive n sizes bids weights hb hw budget fallback hf) epsilon label bits
  fun field => sampled (field.cast (constructed_fields n sizes bids weights hb hn).symm)

theorem sampleRow_feasible (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 < weights j code) (budget : ℚ)
    (fallback : SparseMW.ProductCodes sizes) (hf : SparseMW.productResource bids fallback ≤ budget)
    (epsilon : ℚ) (bits : Fin ((constructed n sizes bids weights hb (fun j code => (hw j code).le)).guideTree.epsilonBitBudget epsilon) → Bool) :
    Feasible (budget : ℝ) (fun field => (sampleRow n sizes bids weights hb hw budget fallback hf epsilon bits field : ℝ)) := by
  let hn := fun j code => (hw j code).le
  let tree := constructed n sizes bids weights hb hn
  let label := (constructedLabelEquiv n sizes bids weights hb hn).symm fallback
  have hFallback : tree.resource label ≤ budget := by
    rw [constructed_resource, Equiv.apply_symm_apply]
    exact hf
  have h := tree.epsilonRow_feasible (constructed_certified n sizes bids weights hb hn) budget
    (constructed_prefix_positive n sizes bids weights hb hw budget fallback hf) epsilon label hFallback bits
  constructor
  · intro field
    exact h.1 (field.cast (constructed_fields n sizes bids weights hb hn).symm)
  · have hSum := Equiv.sum_comp (finCastEquiv (constructed_fields n sizes bids weights hb hn).symm)
      (fun field => (tree.epsilonRow (constructed_certified n sizes bids weights hb hn) budget
        (constructed_prefix_positive n sizes bids weights hb hw budget fallback hf) epsilon label bits field : ℝ))
    exact hSum.trans_le h.2

theorem sampleRow_event_error (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 < weights j code) (budget : ℚ)
    (fallback : SparseMW.ProductCodes sizes) (hf : SparseMW.productResource bids fallback ≤ budget)
    (epsilon : ℚ) (he : 0 < epsilon) (event : Set (Allocation (n + 1))) (hEvent : MeasurableSet event) :
    |(fairBitKernel ((constructed n sizes bids weights hb (fun j code => (hw j code).le)).guideTree.epsilonBitBudget epsilon)).mean
      (fun bits => if (fun field => (sampleRow n sizes bids weights hb hw budget fallback hf epsilon bits field : ℝ)) ∈ event then 1 else 0) -
      ((SparseMW.gibbsWholeRowLaw bids budget fallback hf weights hw).law : Measure (Allocation (n + 1))).real event| ≤ (epsilon : ℝ) := by
  let hn := fun j code => (hw j code).le
  let tree := constructed n sizes bids weights hb hn
  let label := (constructedLabelEquiv n sizes bids weights hb hn).symm fallback
  have h := tree.epsilonRow_event_error (constructed_certified n sizes bids weights hb hn) budget
    (constructed_prefix_positive n sizes bids weights hb hw budget fallback hf) epsilon he label
      {row | (fun field : Fin (n + 1) => row (field.cast (constructed_fields n sizes bids weights hb hn).symm)) ∈ event}
  have hTarget := constructed_target_row_mean n sizes bids weights hb hw budget fallback hf
    (fun row => if row ∈ event then 1 else 0)
  have hLaw := (SparseMW.gibbsWholeRowLaw bids budget fallback hf weights hw).law_event event hEvent
  change _ = ∑ i, _ at hLaw
  dsimp only at hTarget
  simp only [Set.mem_ofPred_eq] at h
  dsimp only [tree, hn] at h
  rw [hTarget, ← hLaw] at h
  exact h

theorem sampleRow_cdf_error (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 < weights j code) (budget : ℚ)
    (fallback : SparseMW.ProductCodes sizes) (hf : SparseMW.productResource bids fallback ≤ budget)
    (epsilon : ℚ) (he : 0 < epsilon) (field : Fin (n + 1)) (threshold : ℝ) :
    |(fairBitKernel ((constructed n sizes bids weights hb (fun j code => (hw j code).le)).guideTree.epsilonBitBudget epsilon)).mean
      (fun bits => if (sampleRow n sizes bids weights hb hw budget fallback hf epsilon bits field : ℝ) ≤ threshold then 1 else 0) -
      closedCDF (SparseMW.gibbsWholeRowLaw bids budget fallback hf weights hw).law field threshold| ≤ (epsilon : ℝ) := by
  have h := sampleRow_event_error n sizes bids weights hb hw budget fallback hf epsilon he
    {row | row field ≤ threshold} (measurableSet_le (measurable_pi_apply field) measurable_const)
  unfold closedCDF marginal
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [map_measureReal_apply (measurable_pi_apply field) measurableSet_Iic]
  exact h

end ProductArrayTree
end Blotto
