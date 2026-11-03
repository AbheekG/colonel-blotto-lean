import Blotto.PlayerSpecificFiniteSamplerContract
import Blotto.IndependentWholeSamplers
import Blotto.FairBitProductLaw

/-! Actual laws of the public rational sampler use complete fresh fair-bit
vectors. Disjoint player packets give the product of whole allocation
laws, preserving all dependence among one player's coordinates. -/
namespace Blotto.PlayerSpecificFiniteSamplerLaw
open MeasureTheory PlayerSpecificFiniteSampler
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def sample {N : ℕ} (p : Prepared N) (player : Bool) (bits : Fin (bitCount p) → Bool) : Allocation N :=
  PlayerSpecificRationalOutput.allocation (draw p player bits)

noncomputable def law {N : ℕ} (p : Prepared N) (player : Bool) : Mixed N :=
  (fairBitLaw (bitCount p)).map (sample p player)

theorem measurable_sample {N : ℕ} (p : Prepared N) (player : Bool) : Measurable (sample p player) :=
  measurable_of_countable _

theorem supported {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) (p : Prepared N)
    (hp : prepare i epsilon=some p) (player : Bool) :
    Supported (if player then 1 else (i.budget:ℝ)) (law p player) := by
  obtain ⟨hbudget,x,hx,hdraw⟩ := PlayerSpecificFiniteSamplerContract.accepted_draws i epsilon p hp
  change ∀ᵐ y ∂Measure.map (sample p player) (fairBitLaw (bitCount p) : Measure (Fin (bitCount p) → Bool)),
    Blotto.Feasible (if player then 1 else (i.budget:ℝ)) y
  rw [ae_map_iff (measurable_sample p player).aemeasurable (measurable_feasible _)]
  exact Filter.Eventually.of_forall (fun bits => (hdraw player bits).1)

noncomputable def joint {N : ℕ} (p : Prepared N) : ProbabilityMeasure (Allocation N × Allocation N) :=
  (fairBitLaw (bitCount p+bitCount p)).map (fun bits =>
    (sample p true (firstBitBlock (bitCount p) (bitCount p) bits),
      sample p false (secondBitBlock (bitCount p) (bitCount p) bits)))

theorem joint_product {N : ℕ} (p : Prepared N) :
    (joint p : Measure (Allocation N × Allocation N))=
      (law p true : Measure (Allocation N)).prod (law p false : Measure (Allocation N)) :=
  fairBitBlocks_map_product (bitCount p) (bitCount p) (sample p true) (sample p false)

theorem independent_player_packets {N : ℕ} (p : Prepared N) :
    Measure.map (Prod.map (sample p true) (sample p false))
      ((fairBitLaw (bitCount p) : Measure (Fin (bitCount p) → Bool)).prod
        (fairBitLaw (bitCount p) : Measure (Fin (bitCount p) → Bool)))=
      (law p true : Measure (Allocation N)).prod (law p false : Measure (Allocation N)) :=
  independent_seed_pair_law (bitCount p) (bitCount p) (sample p true) (sample p false)

end Blotto.PlayerSpecificFiniteSamplerLaw
