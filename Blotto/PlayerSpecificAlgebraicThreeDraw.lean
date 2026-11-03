import Blotto.PlayerSpecificAlgebraicThreeDescriptorSizes

/-! Actual three-variable core sampling for both coordinate orders and
the exceptional case. Every bit string is feasible and has one original-
input height bound. Law approximation and complete source prices remain. -/
namespace Blotto.PlayerSpecificAlgebraicThreeDraw
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicThreeInput
open PlayerSpecificAlgebraicThreeEnvironmentSizes
open PlayerSpecificAlgebraicCandidates (Candidate)
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def draw (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ) (bits : Fin (8*H+K) → Bool) : FixedArrayTable 3 Data :=
  PlayerSpecificAlgebraicSegmentSample.sample model root (PlayerSpecificAlgebraicUnorderedThree.prepare model root a) 8 H K bits

theorem every_path (model : RationalCostModel) (root : Candidate) (a : Input) (i : ThreeSpec)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicUnorderedThree.Values a i x) (H K : ℕ) (bits : Fin (8*H+K) → Bool) :
    FullBudget i.B (values (draw model root a H K bits) x) ∧
      InBox ![i.a,i.d,i.c] (values (draw model root a H K bits) x) := by
  have hf:=PlayerSpecificAlgebraicUnorderedThree.fields model root a i hm hirr hv x hx ha
  have hP : ∀ slot,values ((PlayerSpecificAlgebraicUnorderedThree.prepare model root a).first.read slot) x=i.segmentLottery.P slot := by
    intro slot; funext j; exact hf.2.1 slot j
  have hQ : ∀ slot,values ((PlayerSpecificAlgebraicUnorderedThree.prepare model root a).second.read slot) x=i.segmentLottery.Q slot := by
    intro slot; funext j; exact hf.2.2 slot j
  constructor
  · apply PlayerSpecificAlgebraicSegmentSample.budget model root (PlayerSpecificAlgebraicUnorderedThree.prepare model root a) 8 H K bits x i.B hx.1
    · intro slot; rw [hP]; exact i.segmentLottery_endpoints.1 slot
    · intro slot; rw [hQ]; exact i.segmentLottery_endpoints.2 slot
  · apply PlayerSpecificAlgebraicSegmentSample.box model root (PlayerSpecificAlgebraicUnorderedThree.prepare model root a) 8 H K bits x ![i.a,i.d,i.c] hx.1
    · intro slot; rw [hP]; exact i.segmentLottery_box.1 slot
    · intro slot; rw [hQ]; exact i.segmentLottery_box.2 slot


def height (T K : ℕ) : ℕ := iterate 3 (iterate 20 T+2*K+6)
def coefficient : ℕ := (PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3*
  ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^20+8)

theorem height_linear (T K : ℕ) : height T K+1≤coefficient*(T+K+1) := by
  have hi:=iterate_bound 20 T
  have ho:=iterate_bound 3 (iterate 20 T+2*K+6)
  have hA : 1≤(PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^20 := Nat.succ_le_of_lt (pow_pos (Nat.succ_pos _) 20)
  have he : iterate 20 T+2*K+6+1≤((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^20+8)*(T+K+1) := by
    nlinarith only [hi,hA,Nat.zero_le T,Nat.zero_le K]
  exact ho.trans (by simpa only [coefficient,mul_assoc] using
    Nat.mul_le_mul_left ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3) he)


theorem heights (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ)
    (bits : Fin (8*H+K) → Bool) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4) (T : ℕ) (hmT : HasHeight root.polynomial T) (hT : 2≤T) (hfit : Fits root a T) :
    ∀ j,HasHeight ((draw model root a H K bits).read j) (height T K) := by
  have hd:=PlayerSpecificAlgebraicThreeDescriptorSizes.unordered model root a T hfit hm hm0 hml hmT hT
  exact PlayerSpecificAlgebraicSegmentHeights.sample model root (PlayerSpecificAlgebraicUnorderedThree.prepare model root a)
    8 H K bits hm hm0 hml (iterate 20 T) (mono hmT (PlayerSpecificAlgebraicExpressionBudget.initial_le 20 T))
      hd.first hd.second


theorem reduced (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ)
    (bits : Fin (8*H+K) → Bool) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) :
    ∀ j,Reduced root.polynomial ((draw model root a H K bits).read j) := by
  intro j
  unfold draw PlayerSpecificAlgebraicSegmentSample.sample interpolate
  rw [FixedArrayTable.read_ofFn]
  exact PlayerSpecificAlgebraicField.plus_reduced _ _ _ hm hm0


theorem random_bit_budget (N H K : ℕ) : 8*H+K≤(N+1000)*H+2*K := by
  have h : 8≤N+1000 := by omega
  have hm:=Nat.mul_le_mul_right H h
  omega

end Blotto.PlayerSpecificAlgebraicThreeDraw
