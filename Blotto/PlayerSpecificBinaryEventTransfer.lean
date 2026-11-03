import Blotto.PlayerSpecificIdealResourceEventTransfer

/-! Whole-event comparison for one actual algebraic coin followed by
complete fresh continuations, and for exact binary mixtures. -/
namespace Blotto.PlayerSpecificBinaryEventTransfer
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem binary {N : ℕ} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (u l v w : Mixed N) (E : ℝ)
    (hu : PlayerSpecificEventDistance.Bound u v E) (hl : PlayerSpecificEventDistance.Bound l w E) :
    PlayerSpecificEventDistance.Bound (binaryLaw p hp u l) (binaryLaw p hp v w) E := by
  intro A hA
  rw [PlayerSpecificResourceIdealLaw.binary_event p hp u l A hA,PlayerSpecificResourceIdealLaw.binary_event p hp v w A hA]
  have h := PlayerSpecificAlgebraicCoinExpectation.mixture_error p p _ _ _ _ E 0 hp
    (PlayerSpecificResourceIdealLaw.event_bounds v A) (PlayerSpecificResourceIdealLaw.event_bounds w A)
    (hu A hA) (hl A hA) (by simp)
  simpa only [zero_add] using h

theorem actual_choice {N : ℕ} (model : RationalCostModel) (root : Candidate) (probability : Data) (H S : ℕ)
    (upper lower : (Fin S → Bool) → Allocation N)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (hp : 0 ≤ realEvaluate probability x ∧ realEvaluate probability x ≤ 1)
    (u l : Mixed N) (E : ℝ)
    (hu : PlayerSpecificEventDistance.Bound ((fairBitLaw S).map upper) u E)
    (hl : PlayerSpecificEventDistance.Bound ((fairBitLaw S).map lower) l E) :
    PlayerSpecificEventDistance.Bound (PlayerSpecificBinaryDrawLaw.law model root probability H S upper lower)
      (binaryLaw (realEvaluate probability x) hp u l) (1/(2:ℝ)^H+E) := by
  intro A hA
  rw [PlayerSpecificBinaryDrawLaw.event model root probability H S upper lower A hA,
    PlayerSpecificResourceIdealLaw.binary_event _ hp u l A hA]
  exact PlayerSpecificAlgebraicCoinExpectation.mixture_error _ _ _ _ _ _ E (1/(2:ℝ)^H)
    (PlayerSpecificAlgebraicCoinExpectation.success_bounds H (PlayerSpecificAlgebraicMidpointCoin.run model root probability H))
    (PlayerSpecificResourceIdealLaw.event_bounds u A) (PlayerSpecificResourceIdealLaw.event_bounds l A)
    (hu A hA) (hl A hA) (PlayerSpecificAlgebraicMidpointCoin.paper_discrepancy model root probability H hm hirr hv x hx hp)

end Blotto.PlayerSpecificBinaryEventTransfer
