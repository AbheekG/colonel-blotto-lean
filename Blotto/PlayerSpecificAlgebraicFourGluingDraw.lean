import Blotto.PlayerSpecificAlgebraicFourGluingTable

/-! Actual bounded-bit normal-branch four-variable sampling. Safe
fallback endpoints preserve the hard budget even on zero-weight slots. -/
namespace Blotto.PlayerSpecificAlgebraicFourGluingDraw
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicFourInput
open PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def draw (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ)
    (bits : Fin (80*H+K) → Bool) : FixedArrayTable 4 Data :=
  PlayerSpecificAlgebraicSegmentSample.sample model root (PlayerSpecificAlgebraicFourGluingTable.prepare model root a) 80 H K bits

theorem every_path (model : RationalCostModel) (root : Candidate) (a : Input) (i : FourInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T)
    (hcase : (1-i.p)*i.ell ≤ i.w) (H K : ℕ) (bits : Fin (80*H+K) → Bool) :
    FullBudget i.B (values (draw model root a H K bits) x) := by
  have hr := PlayerSpecificAlgebraicFourGluingTable.refines model root a i hm hirr hv x hx ha T hfit hml hmT hT hcase
  exact PlayerSpecificAlgebraicDescriptorReference.sample_budget model root
    (PlayerSpecificAlgebraicFourGluingTable.prepare model root a) 80 H K bits x i.B _ hr hx.1
    (i.gluingDescriptor_endpoints hcase).1 (i.gluingDescriptor_endpoints hcase).2

def height (T K : ℕ) : ℕ := iterate 3 (iterate 43 T+2*K+6)
def coefficient : ℕ := (PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3*
  ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^43+8)

theorem height_linear (T K : ℕ) : height T K+1 ≤ coefficient*(T+K+1) := by
  have hi := iterate_bound 43 T
  have ho := iterate_bound 3 (iterate 43 T+2*K+6)
  have hA : 1 ≤ (PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^43 := Nat.succ_le_of_lt (pow_pos (Nat.succ_pos _) 43)
  have he : iterate 43 T+2*K+6+1 ≤ ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^43+8)*(T+K+1) := by
    nlinarith only [hi,hA,Nat.zero_le T,Nat.zero_le K]
  exact ho.trans (by simpa only [coefficient,mul_assoc] using
    Nat.mul_le_mul_left ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3) he)

theorem heights (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) (H K : ℕ) (bits : Fin (80*H+K) → Bool) :
    ∀ j,HasHeight ((draw model root a H K bits).read j) (height T K) := by
  have hd := PlayerSpecificAlgebraicFourGluingTable.bounds model root a T ha hm hm0 hml hmT hT
  exact PlayerSpecificAlgebraicSegmentHeights.sample model root (PlayerSpecificAlgebraicFourGluingTable.prepare model root a)
    80 H K bits hm hm0 hml (iterate 43 T) (mono hmT (PlayerSpecificAlgebraicExpressionBudget.initial_le 43 T))
      hd.first hd.second

theorem reduced (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ)
    (bits : Fin (80*H+K) → Bool) (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) :
    ∀ j,Reduced root.polynomial ((draw model root a H K bits).read j) := by
  intro j
  unfold draw PlayerSpecificAlgebraicSegmentSample.sample interpolate
  rw [FixedArrayTable.read_ofFn]
  exact PlayerSpecificAlgebraicField.plus_reduced _ _ _ hm hm0

theorem random_bit_budget (N H K : ℕ) : 80*H+K ≤ (N+1000)*H+2*K := by
  have h := Nat.mul_le_mul_right H (show 80 ≤ N+1000 by omega)
  omega

end Blotto.PlayerSpecificAlgebraicFourGluingDraw
