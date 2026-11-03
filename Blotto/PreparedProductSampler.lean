import Blotto.ProductArrayTreeLaw

/-! Guide preparation and drawing are distinct native operations. Prepared data
stores the constructed tree, budget and fallback once; each draw traverses this
stored tree and never calls the guide constructor. Preparation/draw pricing and
compact source leaf representations remain separate obligations. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators Classical

structure PreparedProductSampler (fields : ℕ) where
  tree : ProductBidTree
  fields_eq : tree.fields = fields
  budget : ℚ
  certified : tree.guideTree.real.LowerCertified
  positive_mass : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)
  fallback : Fin tree.labels
  fallback_feasible : tree.resource fallback ≤ budget

namespace PreparedProductSampler

def bitBudget {m : ℕ} (prepared : PreparedProductSampler m) (epsilon : ℚ) : ℕ :=
  prepared.tree.guideTree.epsilonBitBudget epsilon

def sample {m : ℕ} (prepared : PreparedProductSampler m) (epsilon : ℚ)
    (bits : Fin (prepared.bitBudget epsilon) → Bool) : Fin m → ℚ :=
  fun field => prepared.tree.epsilonRow prepared.certified prepared.budget prepared.positive_mass epsilon
    prepared.fallback bits (field.cast prepared.fields_eq.symm)

theorem sample_feasible {m : ℕ} (prepared : PreparedProductSampler m) (epsilon : ℚ)
    (bits : Fin (prepared.bitBudget epsilon) → Bool) :
    Feasible (prepared.budget : ℝ) (fun field => (prepared.sample epsilon bits field : ℝ)) := by
  have h := prepared.tree.epsilonRow_feasible prepared.certified prepared.budget prepared.positive_mass epsilon
    prepared.fallback prepared.fallback_feasible bits
  constructor
  · intro field; exact h.1 (field.cast prepared.fields_eq.symm)
  · have he := Equiv.sum_comp (ProductArrayTree.finCastEquiv prepared.fields_eq.symm)
      (fun field => (prepared.tree.epsilonRow prepared.certified prepared.budget prepared.positive_mass epsilon
        prepared.fallback bits field : ℝ))
    exact he.trans_le h.2

noncomputable def sampleLaw {m : ℕ} (prepared : PreparedProductSampler m) (epsilon : ℚ) : Mixed m :=
  (fairBitLaw (prepared.bitBudget epsilon)).map (fun bits field => (prepared.sample epsilon bits field : ℝ))

theorem sampleLaw_supported {m : ℕ} (prepared : PreparedProductSampler m) (epsilon : ℚ) :
    Supported (prepared.budget : ℝ) (prepared.sampleLaw epsilon) := by
  change ∀ᵐ row ∂Measure.map (fun bits field => (prepared.sample epsilon bits field : ℝ))
    (fairBitLaw (prepared.bitBudget epsilon) : Measure (Fin (prepared.bitBudget epsilon) → Bool)), Feasible (prepared.budget : ℝ) row
  rw [ae_map_iff (measurable_of_countable _).aemeasurable (ProductBidTree.feasible_measurable (prepared.budget : ℝ))]
  exact Filter.Eventually.of_forall (prepared.sample_feasible epsilon)

theorem sampleLaw_event {m : ℕ} (prepared : PreparedProductSampler m) (epsilon : ℚ)
    (event : Set (Allocation m)) (hEvent : MeasurableSet event) :
    (prepared.sampleLaw epsilon : Measure (Allocation m)).real event =
      (fairBitKernel (prepared.bitBudget epsilon)).mean
        (fun bits => if (fun field => (prepared.sample epsilon bits field : ℝ)) ∈ event then 1 else 0) := by
  change (Measure.map (fun bits field => (prepared.sample epsilon bits field : ℝ))
    (fairBitLaw (prepared.bitBudget epsilon) : Measure (Fin (prepared.bitBudget epsilon) → Bool))).real event = _
  rw [map_measureReal_apply (measurable_of_countable _) hEvent]
  change _ = ∫ bits, _ ∂(fairBitLaw (prepared.bitBudget epsilon) : Measure (Fin (prepared.bitBudget epsilon) → Bool))
  have he : (fun bits : Fin (prepared.bitBudget epsilon) → Bool =>
      if (fun field => (prepared.sample epsilon bits field : ℝ)) ∈ event then (1 : ℝ) else 0) =
      ((fun bits field => (prepared.sample epsilon bits field : ℝ)) ⁻¹' event).indicator (fun _ => 1) := by
    funext bits; rfl
  rw [he, integral_indicator_const _ (hEvent.preimage (measurable_of_countable _)), smul_eq_mul, mul_one]

end PreparedProductSampler

namespace ProductArrayTree

def prepareSampler (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 < weights j code) (budget : ℚ)
    (fallback : SparseMW.ProductCodes sizes) (hf : SparseMW.productResource bids fallback ≤ budget) :
    PreparedProductSampler (n + 1) where
  tree := constructed n sizes bids weights hb (fun j code => (hw j code).le)
  fields_eq := constructed_fields n sizes bids weights hb (fun j code => (hw j code).le)
  budget := budget
  certified := constructed_certified n sizes bids weights hb (fun j code => (hw j code).le)
  positive_mass := constructed_prefix_positive n sizes bids weights hb hw budget fallback hf
  fallback := (constructedLabelEquiv n sizes bids weights hb (fun j code => (hw j code).le)).symm fallback
  fallback_feasible := by
    rw [constructed_resource, Equiv.apply_symm_apply]
    exact hf

theorem prepareSampler_sample (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 < weights j code) (budget : ℚ)
    (fallback : SparseMW.ProductCodes sizes) (hf : SparseMW.productResource bids fallback ≤ budget)
    (epsilon : ℚ) (bits : Fin ((prepareSampler n sizes bids weights hb hw budget fallback hf).bitBudget epsilon) → Bool) :
    (prepareSampler n sizes bids weights hb hw budget fallback hf).sample epsilon bits =
      sampleRow n sizes bids weights hb hw budget fallback hf epsilon bits := rfl

theorem prepareSampler_event_error (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 < weights j code) (budget : ℚ)
    (fallback : SparseMW.ProductCodes sizes) (hf : SparseMW.productResource bids fallback ≤ budget)
    (epsilon : ℚ) (he : 0 < epsilon) (event : Set (Allocation (n + 1))) (hEvent : MeasurableSet event) :
    |(fairBitKernel ((prepareSampler n sizes bids weights hb hw budget fallback hf).bitBudget epsilon)).mean
      (fun bits => if (fun field => ((prepareSampler n sizes bids weights hb hw budget fallback hf).sample epsilon bits field : ℝ)) ∈ event then 1 else 0) -
      ((SparseMW.gibbsWholeRowLaw bids budget fallback hf weights hw).law : Measure (Allocation (n + 1))).real event| ≤ (epsilon : ℝ) :=
  sampleRow_event_error n sizes bids weights hb hw budget fallback hf epsilon he event hEvent

theorem prepareSampler_CDFClose (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 < weights j code) (budget : ℚ)
    (fallback : SparseMW.ProductCodes sizes) (hf : SparseMW.productResource bids fallback ≤ budget)
    (epsilon : ℚ) (he : 0 < epsilon) :
    CDFClose ((prepareSampler n sizes bids weights hb hw budget fallback hf).sampleLaw epsilon)
      (SparseMW.gibbsWholeRowLaw bids budget fallback hf weights hw).law (epsilon : ℝ) := by
  intro field threshold
  unfold closedCDF marginal
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [map_measureReal_apply (measurable_pi_apply field) measurableSet_Iic,
    map_measureReal_apply (measurable_pi_apply field) measurableSet_Iic]
  change |((prepareSampler n sizes bids weights hb hw budget fallback hf).sampleLaw epsilon : Measure (Allocation (n + 1))).real
    {row | row field ≤ threshold} - ((SparseMW.gibbsWholeRowLaw bids budget fallback hf weights hw).law : Measure (Allocation (n + 1))).real
    {row | row field ≤ threshold}| ≤ (epsilon : ℝ)
  rw [PreparedProductSampler.sampleLaw_event _ _ _ (measurableSet_le (measurable_pi_apply field) measurable_const)]
  exact prepareSampler_event_error n sizes bids weights hb hw budget fallback hf epsilon he
    {row | row field ≤ threshold} (measurableSet_le (measurable_pi_apply field) measurable_const)

theorem prepareSampler_payoff_error (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 < weights j code) (budget : ℚ)
    (fallback : SparseMW.ProductCodes sizes) (hf : SparseMW.productResource bids fallback ≤ budget)
    (epsilon : ℚ) (he : 0 < epsilon) (values : Values (n + 1)) (candidate : Allocation (n + 1)) :
    |purePayoff values candidate ((prepareSampler n sizes bids weights hb hw budget fallback hf).sampleLaw epsilon) -
      purePayoff values candidate (SparseMW.gibbsWholeRowLaw bids budget fallback hf weights hw).law| ≤ (epsilon : ℝ) :=
  purePayoff_close values (prepareSampler_CDFClose n sizes bids weights hb hw budget fallback hf epsilon he) candidate

end ProductArrayTree
end Blotto
