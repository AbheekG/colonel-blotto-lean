import Blotto.PlayerSpecificAlgebraicFourMergedSizes

/-! The actual small uniform component draws the merged three-core and
splits its first coordinate. Every output spends exactly the original budget. -/
namespace Blotto.PlayerSpecificAlgebraicFourMergedDraw
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicFourInput
open PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def draw (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ)
    (bits : Fin (8*H+K) → Bool) : FixedArrayTable 4 Data :=
  let p := PlayerSpecificAlgebraicFourMergedInput.prepare model root a
  let y := PlayerSpecificAlgebraicThreeDraw.draw model root p.child H K bits
  PlayerSpecificAlgebraicSplitFirstTwo.split root p.first p.second y

theorem every_path (model : RationalCostModel) (root : Candidate) (a : Input) (i : FourInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (hcase : i.w < (1-i.p)*i.ell) (H K : ℕ) (bits : Fin (8*H+K) → Bool) :
    FullBudget i.B (values (draw model root a H K bits) x) := by
  let p := PlayerSpecificAlgebraicFourMergedInput.prepare model root a
  let y := PlayerSpecificAlgebraicThreeDraw.draw model root p.child H K bits
  have hp := PlayerSpecificAlgebraicFourMergedInput.values model root a i hm hirr hv x hx ha T hfit hcase
  have hy := PlayerSpecificAlgebraicThreeDraw.every_path model root p.child (i.smallUniformInput hcase).childSpec
    hm hirr hv x hx hp.2.2 H K bits
  have hf : 0 < realEvaluate p.first x := by rw [hp.1]; exact (i.smallUniformInput hcase).l0_pos
  have hs : 0 < realEvaluate p.second x := by rw [hp.2.1]; exact (i.smallUniformInput hcase).l1_pos
  exact PlayerSpecificAlgebraicSplitFirstTwo.budget root p.first p.second y hm hirr x i.B hx.1 hf hs hy.1

def height (T K : ℕ) : ℕ := iterate 6 (iterate 35 T+2*K+6)
def coefficient : ℕ := (PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^6*
  ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^35+8)

theorem height_linear (T K : ℕ) : height T K+1 ≤ coefficient*(T+K+1) := by
  have hi := iterate_bound 35 T
  have ho := iterate_bound 6 (iterate 35 T+2*K+6)
  have hA : 1 ≤ (PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^35 := Nat.succ_le_of_lt (pow_pos (Nat.succ_pos _) 35)
  have he : iterate 35 T+2*K+6+1 ≤ ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^35+8)*(T+K+1) := by
    nlinarith only [hi,hA,Nat.zero_le T,Nat.zero_le K]
  exact ho.trans (by simpa only [coefficient,mul_assoc] using
    Nat.mul_le_mul_left ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^6) he)

theorem bounds (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) (H K : ℕ) (bits : Fin (8*H+K) → Bool) :
    ∀ j,Reduced root.polynomial ((draw model root a H K bits).read j) ∧ HasHeight ((draw model root a H K bits).read j) (height T K) := by
  let p := PlayerSpecificAlgebraicFourMergedInput.prepare model root a
  let y := PlayerSpecificAlgebraicThreeDraw.draw model root p.child H K bits
  have hp := PlayerSpecificAlgebraicFourMergedSizes.bounds model root a T ha hm hm0 hml hmT hT
  have hi := PlayerSpecificAlgebraicExpressionBudget.initial_le 15 T
  have hy := PlayerSpecificAlgebraicThreeDraw.heights model root p.child H K bits hm hm0 hml (iterate 15 T)
    (mono hmT hi) (hT.trans hi) hp.2.2
  have hyr := PlayerSpecificAlgebraicThreeDraw.reduced model root p.child H K bits hm hm0
  change ∀ j,HasHeight (y.read j) (iterate 3 (iterate 20 (iterate 15 T)+2*K+6)) at hy
  rw [PlayerSpecificAlgebraicThreeEnvironmentSizes.iterate_add] at hy
  have h15 : iterate 15 T ≤ iterate 3 (iterate 35 T+2*K+6) :=
    (PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (by omega : 15 ≤ 35)).trans
      ((show iterate 35 T ≤ iterate 35 T+2*K+6 by omega).trans (PlayerSpecificAlgebraicExpressionBudget.initial_le 3 _))
  have hb := PlayerSpecificAlgebraicSplitFirstTwo.bounds root p.first p.second y _ hm hm0 hml
    (mono hmT (hi.trans h15)) ((show 1 ≤ T by omega).trans (hi.trans h15))
    ⟨hp.1.1,mono hp.1.2 h15⟩ ⟨hp.2.1.1,mono hp.2.1.2 h15⟩ (fun j => ⟨hyr j,hy j⟩)
  rw [PlayerSpecificAlgebraicThreeEnvironmentSizes.iterate_add] at hb
  exact hb

theorem random_bit_budget (N H K : ℕ) : 8*H+K ≤ (N+1000)*H+2*K :=
  PlayerSpecificAlgebraicThreeDraw.random_bit_budget N H K

end Blotto.PlayerSpecificAlgebraicFourMergedDraw
