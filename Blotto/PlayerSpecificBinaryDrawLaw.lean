import Blotto.PlayerSpecificResourceContinuationCDF

/-! One actual algebraic midpoint coin selects a complete fresh-suffix
allocation sampler. Its local error adds to the branch CDF error. -/
namespace Blotto.PlayerSpecificBinaryDrawLaw
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def law {N : ℕ} (model : RationalCostModel) (root : Candidate) (probability : Data) (H S : ℕ)
    (upper lower : (Fin S → Bool) → Allocation N) : Mixed N :=
  (fairBitLaw (H+S)).map (fun bits =>
    if PlayerSpecificAlgebraicMidpointCoin.run model root probability H (firstBitBlock H S bits)
      then upper (secondBitBlock H S bits) else lower (secondBitBlock H S bits))

theorem event {N : ℕ} (model : RationalCostModel) (root : Candidate) (probability : Data) (H S : ℕ)
    (upper lower : (Fin S → Bool) → Allocation N) (A : Set (Allocation N)) (hA : MeasurableSet A) :
    (law model root probability H S upper lower : Measure (Allocation N)).real A=
      PlayerSpecificAlgebraicMidpointCoin.success model root probability H*((fairBitLaw S).map upper : Measure (Allocation N)).real A+
      (1-PlayerSpecificAlgebraicMidpointCoin.success model root probability H)*((fairBitLaw S).map lower : Measure (Allocation N)).real A := by
  rw [law,PlayerSpecificFairAveraging.event _ _ A hA]
  have he : ∀ bits : Fin (H+S) → Bool,
      (if (if PlayerSpecificAlgebraicMidpointCoin.run model root probability H (firstBitBlock H S bits)
          then upper (secondBitBlock H S bits) else lower (secondBitBlock H S bits)) ∈ A then (1:ℝ) else 0)=
        if PlayerSpecificAlgebraicMidpointCoin.run model root probability H (firstBitBlock H S bits)
          then (if upper (secondBitBlock H S bits) ∈ A then (1:ℝ) else 0)
          else (if lower (secondBitBlock H S bits) ∈ A then (1:ℝ) else 0) := by
    intro bits
    cases PlayerSpecificAlgebraicMidpointCoin.run model root probability H (firstBitBlock H S bits) <;> rfl
  simp_rw [he]
  rw [PlayerSpecificFairBitBlocks.binary_continuation H S (PlayerSpecificAlgebraicMidpointCoin.run model root probability H)
    (fun bits => if upper bits ∈ A then (1:ℝ) else 0) (fun bits => if lower bits ∈ A then (1:ℝ) else 0)]
  rw [PlayerSpecificFairAveraging.event S upper A hA,PlayerSpecificFairAveraging.event S lower A hA]
  rfl

theorem CDF_error {N : ℕ} (model : RationalCostModel) (root : Candidate) (probability : Data) (H S : ℕ)
    (upper lower : (Fin S → Bool) → Allocation N)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (hp : 0 ≤ realEvaluate probability x ∧ realEvaluate probability x ≤ 1)
    (u l : Mixed N) (E : ℝ) (hu : CDFClose ((fairBitLaw S).map upper) u E) (hl : CDFClose ((fairBitLaw S).map lower) l E) :
    CDFClose (law model root probability H S upper lower) (binaryLaw (realEvaluate probability x) hp u l)
      (1/(2:ℝ)^H+E) := by
  intro j z
  let A := (fun y : Allocation N => y j) ⁻¹' Set.Iic z
  have hA : MeasurableSet A := (measurable_pi_apply j) measurableSet_Iic
  have hu' : |((fairBitLaw S).map upper : Measure (Allocation N)).real A-(u : Measure (Allocation N)).real A| ≤ E := by
    simpa only [PlayerSpecificResourceContinuationCDF.cdf_event,A] using hu j z
  have hl' : |((fairBitLaw S).map lower : Measure (Allocation N)).real A-(l : Measure (Allocation N)).real A| ≤ E := by
    simpa only [PlayerSpecificResourceContinuationCDF.cdf_event,A] using hl j z
  rw [PlayerSpecificResourceContinuationCDF.cdf_event,PlayerSpecificResourceContinuationCDF.cdf_event]
  rw [event model root probability H S upper lower A hA,PlayerSpecificResourceIdealLaw.binary_event _ _ _ _ A hA]
  exact PlayerSpecificAlgebraicCoinExpectation.mixture_error _ _ _ _ _ _ E (1/(2:ℝ)^H)
    (PlayerSpecificAlgebraicCoinExpectation.success_bounds H (PlayerSpecificAlgebraicMidpointCoin.run model root probability H))
    (PlayerSpecificResourceIdealLaw.event_bounds u A) (PlayerSpecificResourceIdealLaw.event_bounds l A) hu' hl'
    (PlayerSpecificAlgebraicMidpointCoin.paper_discrepancy model root probability H hm hirr hv x hx hp)

end Blotto.PlayerSpecificBinaryDrawLaw
