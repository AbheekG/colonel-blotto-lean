import Blotto.PlayerSpecificFairBitBlocks

/-! A reached native algebraic coin mixes complete future continuations.
Its local midpoint discrepancy adds at most 2^-H to a uniform bound on
the future error, without assuming that later branch parameters are fixed. -/
namespace Blotto.PlayerSpecificAlgebraicCoinExpectation
open MeasureTheory
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem unit_mean (H : ℕ) (f : (Fin H → Bool) → ℝ) (hf : ∀ bits,0 ≤ f bits ∧ f bits ≤ 1) :
    0 ≤ (∫ bits,f bits ∂(fairBitLaw H : Measure (Fin H → Bool))) ∧
      (∫ bits,f bits ∂(fairBitLaw H : Measure (Fin H → Bool))) ≤ 1 := by
  constructor
  · exact integral_nonneg (fun bits => (hf bits).1)
  · have h := integral_mono (μ := (fairBitLaw H : Measure (Fin H → Bool))) Integrable.of_finite Integrable.of_finite
      (fun bits => (hf bits).2)
    simpa only [integral_const,probReal_univ,one_smul] using h

theorem success_bounds (H : ℕ) (coin : (Fin H → Bool) → Bool) :
    0 ≤ PlayerSpecificFairBitBlocks.success H coin ∧ PlayerSpecificFairBitBlocks.success H coin ≤ 1 := by
  rw [← PlayerSpecificFairBitBlocks.indicator_mean]
  apply unit_mean
  intro bits
  cases coin bits <;> norm_num

theorem mixture_error (q p A B a b E D : ℝ) (hq : 0 ≤ q ∧ q ≤ 1)
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hA : |A-a| ≤ E) (hB : |B-b| ≤ E) (hD : |q-p| ≤ D) :
    |q*A+(1-q)*B-(p*a+(1-p)*b)| ≤ D+E := by
  have hq' : 0 ≤ 1-q := sub_nonneg.mpr hq.2
  have hdiff : |a-b| ≤ 1 := abs_le.mpr ⟨by linarith only [ha.1,hb.2],by linarith only [ha.2,hb.1]⟩
  have hfirst : |q*(A-a)| ≤ q*E := by
    rw [abs_mul,abs_of_nonneg hq.1]
    exact mul_le_mul_of_nonneg_left hA hq.1
  have hsecond : |(1-q)*(B-b)| ≤ (1-q)*E := by
    rw [abs_mul,abs_of_nonneg hq']
    exact mul_le_mul_of_nonneg_left hB hq'
  have hcoin : |(q-p)*(a-b)| ≤ D := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hdiff (abs_nonneg (q-p))).trans (by simpa only [mul_one] using hD)
  have he : q*A+(1-q)*B-(p*a+(1-p)*b)=q*(A-a)+(1-q)*(B-b)+(q-p)*(a-b) := by ring
  rw [he]
  calc
    _ ≤ (|q*(A-a)|+|(1-q)*(B-b)|)+|(q-p)*(a-b)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ q*E+(1-q)*E+D := add_le_add (add_le_add hfirst hsecond) hcoin
    _ = D+E := by ring

theorem native_step (model : RationalCostModel) (root : Candidate) (probability : Data) (H S : ℕ)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (hp : 0 ≤ realEvaluate probability x ∧ realEvaluate probability x ≤ 1)
    (upper lower : (Fin S → Bool) → ℝ) (a b E : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hA : |(∫ bits,upper bits ∂(fairBitLaw S : Measure (Fin S → Bool)))-a| ≤ E)
    (hB : |(∫ bits,lower bits ∂(fairBitLaw S : Measure (Fin S → Bool)))-b| ≤ E) :
    |(∫ bits,(if PlayerSpecificAlgebraicMidpointCoin.run model root probability H (firstBitBlock H S bits)
        then upper (secondBitBlock H S bits) else lower (secondBitBlock H S bits))
      ∂(fairBitLaw (H+S) : Measure (Fin (H+S) → Bool)))-
      (realEvaluate probability x*a+(1-realEvaluate probability x)*b)| ≤ 1/(2:ℝ)^H+E := by
  rw [PlayerSpecificFairBitBlocks.binary_continuation]
  apply mixture_error _ _ _ _ a b E _ (success_bounds H _) ha hb hA hB
  exact PlayerSpecificAlgebraicMidpointCoin.paper_discrepancy model root probability H hm hirr hv x hx hp

end Blotto.PlayerSpecificAlgebraicCoinExpectation
