import Blotto.PlayerSpecificAlgebraicFourSmallDraw

/-! Actual ordered four-variable dispatch uses the paper's exact guard.
Both branches preserve every-output budgets with polynomial coefficient sizes. -/
namespace Blotto.PlayerSpecificAlgebraicOrderedFourDraw
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicFourInput
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def normal (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) : Bool :=
  let complement := PlayerSpecificAlgebraicField.minus r.root.polynomial (PlayerSpecificAlgebraicField.constant r.root.polynomial 1) a.probability
  PlayerSpecificAlgebraicPairStep.le RationalCostModel.schoolbook r.root
    (PlayerSpecificAlgebraicField.times r.root.polynomial complement a.length) a.third

theorem normal_correct (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) : normal r a=true ↔ (1-i.p)*i.ell ≤ i.w := by
  rw [normal,PlayerSpecificAlgebraicPairStep.le_correct RationalCostModel.schoolbook r.root _ _ hm hirr hv x hx,
    PlayerSpecificAlgebraicField.times_value _ _ _ x hx.1,PlayerSpecificAlgebraicField.minus_value _ _ _ x hx.1,
    PlayerSpecificAlgebraicField.constant_value _ _ x hx.1,Rat.cast_one,ha.probability,ha.length,ha.third]

theorem small_bit_bound (H K : ℕ) : PlayerSpecificAlgebraicFourSmallDraw.bitCount H K ≤ (80*H+K)+K := by
  unfold PlayerSpecificAlgebraicFourSmallDraw.bitCount PlayerSpecificAlgebraicFourSmallDraw.remaining
  omega

def draw (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin ((80*H+K)+K) → Bool) : FixedArrayTable 4 Data :=
  if normal r a then PlayerSpecificAlgebraicFourGluingDraw.draw RationalCostModel.schoolbook r.root a H K
    (firstBitBlock (80*H+K) K bits)
  else PlayerSpecificAlgebraicFourSmallDraw.draw r a H K (PlayerSpecificAlgebraicFourSmallDraw.takeBits (small_bit_bound H K) bits)

theorem every_path (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T)
    (H K : ℕ) (bits : Fin ((80*H+K)+K) → Bool) : FullBudget i.B (values (draw r a H K bits) x) := by
  have hc := normal_correct r a i hm hirr hv x hx ha
  by_cases hcase : (1-i.p)*i.ell ≤ i.w
  · rw [draw,ite_eq_left (hc.mpr hcase)]
    exact PlayerSpecificAlgebraicFourGluingDraw.every_path RationalCostModel.schoolbook r.root a i hm hirr hv x hx
      ha T hfit hml hmT hT hcase H K _
  · rw [draw,ite_eq_right (fun h => hcase (hc.mp h))]
    exact PlayerSpecificAlgebraicFourSmallDraw.every_path r a i hm hirr hv x hx ha T hfit hml hmT hT (lt_of_not_ge hcase) H K _

def height (T K : ℕ) : ℕ := max (PlayerSpecificAlgebraicFourGluingDraw.height T K) (PlayerSpecificAlgebraicFourSmallDraw.height T K)
def coefficient : ℕ := PlayerSpecificAlgebraicFourGluingDraw.coefficient+PlayerSpecificAlgebraicFourSmallDraw.coefficient

theorem height_linear (T K : ℕ) : height T K+1 ≤ coefficient*(T+K+1) :=
  PlayerSpecificAlgebraicFourSmallDraw.max_linear _ _ _ _ _ (PlayerSpecificAlgebraicFourGluingDraw.height_linear T K)
    (PlayerSpecificAlgebraicFourSmallDraw.height_linear T K)

theorem bounds (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T)
    (H K : ℕ) (bits : Fin ((80*H+K)+K) → Bool) :
    ∀ j,Reduced r.root.polynomial ((draw r a H K bits).read j) ∧ HasHeight ((draw r a H K bits).read j) (height T K) := by
  have hm0 : r.root.polynomial ≠ [] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hc := normal_correct r a i hm hirr hv x hx ha
  by_cases hcase : (1-i.p)*i.ell ≤ i.w
  · rw [draw,ite_eq_left (hc.mpr hcase)]
    intro j
    have hr := PlayerSpecificAlgebraicFourGluingDraw.reduced RationalCostModel.schoolbook r.root a H K (firstBitBlock (80*H+K) K bits) hm hm0 j
    have hh := PlayerSpecificAlgebraicFourGluingDraw.heights RationalCostModel.schoolbook r.root a T hfit hm hm0 hml hmT hT H K (firstBitBlock (80*H+K) K bits) j
    exact ⟨hr,mono hh (le_max_left _ _)⟩
  · rw [draw,ite_eq_right (fun h => hcase (hc.mp h))]
    intro j
    have h := PlayerSpecificAlgebraicFourSmallDraw.bounds r a i hm hirr hv x hx ha T hfit hml hmT hT (lt_of_not_ge hcase) H K (PlayerSpecificAlgebraicFourSmallDraw.takeBits (small_bit_bound H K) bits) j
    exact ⟨h.1,mono h.2 (le_max_right _ _)⟩

theorem random_bit_budget (N H K : ℕ) : (80*H+K)+K ≤ (N+1000)*H+2*K := by
  have h := Nat.mul_le_mul_right H (show 80 ≤ N+1000 by omega)
  omega

end Blotto.PlayerSpecificAlgebraicOrderedFourDraw
