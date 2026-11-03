import Blotto.PlayerSpecificAlgebraicNestedInteriorSizes

/-! Actual bounded-bit interior nested draw. Its fresh outer and inner
blocks give a single public interface for all three interior cases. -/
namespace Blotto.PlayerSpecificAlgebraicNestedInteriorDraw
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def draw (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ)
    (bits : Fin ((17*H+K)+K) → Bool) : FixedArrayTable 3 Data :=
  let outer := secondBitBlock (17*H+K) K bits
  let table := PlayerSpecificAlgebraicNestedInteriorProfile.prepare model root a K outer
  PlayerSpecificAlgebraicSegmentSample.sample model root table 17 H K (firstBitBlock (17*H+K) K bits)

theorem every_path (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T)
    (H K : ℕ) (bits : Fin ((17*H+K)+K) → Bool) :
    FullBudget i.M (values (draw model root a H K bits) x) ∧ InBox ![i.a,i.d,i.c] (values (draw model root a H K bits) x) := by
  let outer := secondBitBlock (17*H+K) K bits
  let table := PlayerSpecificAlgebraicNestedInteriorProfile.prepare model root a K outer
  have hr := PlayerSpecificAlgebraicNestedInteriorProfile.refines model root a i hm hirr hv x hx ha T hfit hml hmT hT K outer
  have hb := PlayerSpecificAlgebraicNestedInteriorProfile.budget i K outer
  have hxbox := PlayerSpecificAlgebraicNestedInteriorProfile.box i K outer
  exact ⟨PlayerSpecificAlgebraicDescriptorReference.sample_budget model root table 17 H K (firstBitBlock (17*H+K) K bits) x i.M
      _ hr hx.1 (fun slot => (hb slot).1) (fun slot => (hb slot).2),
    PlayerSpecificAlgebraicDescriptorReference.sample_box model root table 17 H K (firstBitBlock (17*H+K) K bits) x ![i.a,i.d,i.c]
      _ hr hx.1 (fun slot => (hxbox slot).1) (fun slot => (hxbox slot).2)⟩

def height (T K : ℕ) : ℕ := iterate 3 (PlayerSpecificAlgebraicNestedInteriorSizes.height T K+2*K+6)

theorem heights (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) (H K : ℕ) (bits : Fin ((17*H+K)+K) → Bool) :
    ∀ j,HasHeight ((draw model root a H K bits).read j) (height T K) := by
  let outer := secondBitBlock (17*H+K) K bits
  let table := PlayerSpecificAlgebraicNestedInteriorProfile.prepare model root a K outer
  have hd := PlayerSpecificAlgebraicNestedInteriorSizes.bounds model root a T ha hm hm0 hml hmT hT K outer
  exact PlayerSpecificAlgebraicSegmentHeights.sample model root table 17 H K (firstBitBlock (17*H+K) K bits) hm hm0 hml
    (PlayerSpecificAlgebraicNestedInteriorSizes.height T K)
    (mono hmT (PlayerSpecificAlgebraicNestedInteriorSizes.input_le T K)) hd.first hd.second

theorem reduced (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ)
    (bits : Fin ((17*H+K)+K) → Bool) (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) :
    ∀ j,Reduced root.polynomial ((draw model root a H K bits).read j) := by
  intro j
  unfold draw PlayerSpecificAlgebraicSegmentSample.sample interpolate
  rw [FixedArrayTable.read_ofFn]
  exact PlayerSpecificAlgebraicField.plus_reduced _ _ _ hm hm0

theorem random_bit_budget (N H K : ℕ) : (17*H+K)+K ≤ (N+1000)*H+2*K := by
  have h := Nat.mul_le_mul_right H (show 17 ≤ N+1000 by omega)
  omega

end Blotto.PlayerSpecificAlgebraicNestedInteriorDraw
