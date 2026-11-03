import Blotto.NestedCoupling
import Blotto.Complementary

/-! Endpoint cases needed by the four-variable reduction. A zero-length
uniform is represented by an actual Dirac law, never by the unnormalized
raw expression uniformLaw 0. -/

namespace Blotto
open MeasureTheory Set

theorem exists_complementary_coupling (M a d : ℝ) (ha : 0 < a) (_hd : 0 < d)
    (haM : a ≤ M) (hdM : d ≤ M) (hmean : a + d = 2 * M) :
    ∃ μ : Mixed 3, (∀ᵐ x ∂(μ : Measure (Allocation 3)), FullBudget M x) ∧
      (marginal μ 0 : Measure ℝ) = uniformLaw a ∧
      (marginal μ 1 : Measure ℝ) = uniformLaw d ∧
      (marginal μ 2 : Measure ℝ) = Measure.dirac 0 := by
  have hM : 0 < M := lt_of_lt_of_le ha haM
  have he := complementary_lengths haM hdM hmean
  have hm := complementaryLaw_marginals M
  refine ⟨complementaryLaw M, complementaryLaw_fullBudget (le_of_lt hM), ?_, ?_, hm.2.2⟩
  · rw [hm.1, affineUniform_zero_uniformLaw hM, he.1]
  · rw [hm.2.1, affineUniform_zero_uniformLaw hM, he.2]

theorem exists_three_coupling_closed (M a d c p : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hc : 0 ≤ c) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (haM : a ≤ M) (hdM : d ≤ M) (hcM : c ≤ M)
    (hbalance : a + d + p * c = 2 * M) :
    ∃ μ : Mixed 3, (∀ᵐ x ∂(μ : Measure (Allocation 3)), FullBudget M x) ∧
      (marginal μ 0 : Measure ℝ) = uniformLaw a ∧
      (marginal μ 1 : Measure ℝ) = uniformLaw d ∧
      (marginal μ 2 : Measure ℝ) = ENNReal.ofReal (1 - p) • Measure.dirac 0 +
        ENNReal.ofReal p • (affineUniform 0 c : Measure ℝ) := by
  by_cases hc0 : 0 < c
  · by_cases hp0 : 0 < p
    · rcases exists_three_coupling M a d c p (lt_of_lt_of_le ha haM) ha hd hc0 hp0
        haM hdM hcM hp1 hbalance with ⟨μ, hμ, h0, h1, h2⟩
      refine ⟨μ, hμ, h0, h1, ?_⟩
      rw [h2, affineUniform_zero_uniformLaw hc0]
      rfl
    · have hpz : p = 0 := le_antisymm (le_of_not_gt hp0) hp
      rcases exists_complementary_coupling M a d ha hd haM hdM (by simpa [hpz] using hbalance)
        with ⟨μ, hμ, h0, h1, h2⟩
      refine ⟨μ, hμ, h0, h1, ?_⟩
      simpa [hpz] using h2
  · have hcz : c = 0 := le_antisymm (le_of_not_gt hc0) hc
    rcases exists_complementary_coupling M a d ha hd haM hdM (by simpa [hcz] using hbalance)
      with ⟨μ, hμ, h0, h1, h2⟩
    refine ⟨μ, hμ, h0, h1, ?_⟩
    rw [h2, hcz, affineUniform_constant, ← add_smul,
      ← ENNReal.ofReal_add (sub_nonneg.mpr hp1) hp]
    simp

/-- All closed parameter cases of the nested construction, including q=0/1,
t=0/c, and an identically zero third marginal. -/
theorem exists_nested_coupling_closed (M a d c t q : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hc : 0 ≤ c) (ht : 0 ≤ t) (htc : t ≤ c)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (haM : a ≤ M) (hdM : d ≤ M) (hcM : c ≤ M)
    (hbalance : a + d + q * t + (1 - q) * c = 2 * M) :
    ∃ μ : Mixed 3, (∀ᵐ x ∂(μ : Measure (Allocation 3)), FullBudget M x) ∧
      (marginal μ 0 : Measure ℝ) = uniformLaw a ∧
      (marginal μ 1 : Measure ℝ) = uniformLaw d ∧
      (marginal μ 2 : Measure ℝ) = ENNReal.ofReal q • (affineUniform 0 t : Measure ℝ) +
        ENNReal.ofReal (1 - q) • (affineUniform 0 c : Measure ℝ) := by
  by_cases hq0 : q = 0
  · rcases exists_three_coupling_closed M a d c 1 ha hd hc (by norm_num) le_rfl haM hdM hcM
      (by simpa [hq0] using hbalance) with ⟨μ, hμ, h0, h1, h2⟩
    refine ⟨μ, hμ, h0, h1, ?_⟩
    simpa [hq0] using h2
  by_cases hqeq : q = 1
  · rcases exists_three_coupling_closed M a d t 1 ha hd ht (by norm_num) le_rfl
      haM hdM (le_trans htc hcM) (by simpa [hqeq] using hbalance) with ⟨μ, hμ, h0, h1, h2⟩
    refine ⟨μ, hμ, h0, h1, ?_⟩
    simpa [hqeq] using h2
  by_cases ht0 : t = 0
  · rcases exists_three_coupling_closed M a d c (1 - q) ha hd hc
      (sub_nonneg.mpr hq1) (by linarith) haM hdM hcM (by simpa [ht0] using hbalance)
      with ⟨μ, hμ, h0, h1, h2⟩
    refine ⟨μ, hμ, h0, h1, ?_⟩
    rw [h2, ht0, affineUniform_constant]
    rw [show (1 - (1 - q) : ℝ) = q by ring]
  by_cases hteq : t = c
  · rcases exists_three_coupling_closed M a d c 1 ha hd hc (by norm_num) le_rfl
      haM hdM hcM (by rw [hteq] at hbalance; nlinarith) with ⟨μ, hμ, h0, h1, h2⟩
    refine ⟨μ, hμ, h0, h1, ?_⟩
    simp only [sub_self, ENNReal.ofReal_zero, zero_smul, ENNReal.ofReal_one, one_smul, zero_add] at h2
    rw [h2, hteq, ← add_smul, ← ENNReal.ofReal_add hq (sub_nonneg.mpr hq1)]
    simp
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have htcp : t < c := lt_of_le_of_ne htc hteq
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  have hqlt : q < 1 := lt_of_le_of_ne hq1 hqeq
  rcases exists_nested_coupling M a d c t q ha hd (lt_of_lt_of_le htp htc) htp htcp hqp hqlt
    haM hdM hcM hbalance with ⟨μ, hμ, h0, h1, h2⟩
  refine ⟨μ, hμ, h0, h1, ?_⟩
  rw [h2, affineUniform_zero_uniformLaw htp,
    affineUniform_zero_uniformLaw (lt_of_lt_of_le htp htc)]

end Blotto
