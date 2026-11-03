import Blotto.PlayerSpecificAlgebraicTerminalCoreFits

/-! The executable terminal dispatcher chooses all four paper cases from
the actual group count and optional fractional coordinate. All branches
share a fixed packet of fresh bits and a four-coordinate output layout. -/
namespace Blotto.PlayerSpecificAlgebraicTerminalCoreDraw
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicTerminalCoreInput PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def bitCount (H K : ℕ) : ℕ := (80*H+K)+K

theorem three_bit_bound (H K : ℕ) : 8*H+K ≤ bitCount H K := by unfold bitCount; omega
theorem midpoint_bit_bound (H K : ℕ) : K ≤ bitCount H K := by unfold bitCount; omega

def draw (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin (bitCount H K) → Bool) : FixedArrayTable 4 Data :=
  if a.count=2 then
    match a.fractional with
    | none => PlayerSpecificAlgebraicComplementaryDraw.draw r.root a.budget K
        (PlayerSpecificAlgebraicFourSmallDraw.takeBits (midpoint_bit_bound H K) bits)
    | some (ell,probability) => PlayerSpecificAlgebraicTerminalEmbedding.mixed
        (PlayerSpecificAlgebraicThreeDraw.draw RationalCostModel.schoolbook r.root (mixedThree a ell probability) H K
          (PlayerSpecificAlgebraicFourSmallDraw.takeBits (three_bit_bound H K) bits))
  else
    match a.fractional with
    | none => PlayerSpecificAlgebraicTerminalEmbedding.uniform
        (PlayerSpecificAlgebraicThreeDraw.draw RationalCostModel.schoolbook r.root (uniformThree r.root a) H K
          (PlayerSpecificAlgebraicFourSmallDraw.takeBits (three_bit_bound H K) bits))
    | some (ell,probability) => PlayerSpecificAlgebraicFourSpecDraw.draw r (mixedFour a ell probability) H K bits

theorem every_path (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : Valid a x) (T : ℕ) (hfit : PlayerSpecificAlgebraicTerminalCoreFits.Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T)
    (H K : ℕ) (bits : Fin (bitCount H K) → Bool) :
    FullBudget (realEvaluate a.budget x) (values (draw r a H K bits) x) := by
  by_cases hc : a.count=2
  · rw [draw,ite_eq_left hc]
    cases hf : a.fractional with
    | none =>
      exact PlayerSpecificAlgebraicComplementaryDraw.every_path r.root a.budget K _ x hx.1 ha.budget.le
    | some pair =>
      obtain ⟨ell,probability⟩ := pair
      let i := mixedSpecTwo a x ha hc ell probability hf
      have hi := PlayerSpecificAlgebraicThreeDraw.every_path RationalCostModel.schoolbook r.root
        (mixedThree a ell probability) i.threeInput hm hirr hv x hx (mixed_two_values a x ha hc ell probability hf) H K
        (PlayerSpecificAlgebraicFourSmallDraw.takeBits (three_bit_bound H K) bits)
      exact PlayerSpecificAlgebraicTerminalEmbedding.mixed_budget _ x _ hi.1
  · have hc3 : a.count=3 := ha.count.resolve_left hc
    rw [draw,ite_eq_right hc]
    cases hf : a.fractional with
    | none =>
      let i := uniformSpec a x ha hc3 hf
      have hi := PlayerSpecificAlgebraicThreeDraw.every_path RationalCostModel.schoolbook r.root
        (uniformThree r.root a) i.threeInput hm hirr hv x hx (uniform_values r.root a x hx.1 ha hc3 hf) H K
        (PlayerSpecificAlgebraicFourSmallDraw.takeBits (three_bit_bound H K) bits)
      exact PlayerSpecificAlgebraicTerminalEmbedding.uniform_budget _ x _ hi.1
    | some pair =>
      obtain ⟨ell,probability⟩ := pair
      let i := mixedSpecThree a x ha hc3 ell probability hf
      exact PlayerSpecificAlgebraicFourSpecDraw.every_path r (mixedFour a ell probability) i.fourInput
        hm hirr hv x hx (mixed_three_values a x ha hc3 ell probability hf) T
        (PlayerSpecificAlgebraicTerminalCoreFits.mixed_three r.root a T hfit ell probability hf) hml hmT hT H K bits

theorem no_fraction_last (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin (bitCount H K) → Bool) (hf : a.fractional=none) : (draw r a H K bits).read 3=[] := by
  by_cases hc : a.count=2
  · simp only [draw,ite_eq_left hc,hf,PlayerSpecificAlgebraicComplementaryDraw.draw,FixedArrayTable.read_ofFn]
    rfl
  · simp only [draw,ite_eq_right hc,hf,PlayerSpecificAlgebraicTerminalEmbedding.uniform,FixedArrayTable.read_ofFn]
    rfl

theorem two_unused (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin (bitCount H K) → Bool) (hc : a.count=2) : (draw r a H K bits).read 2=[] := by
  rw [draw,ite_eq_left hc]
  cases hf : a.fractional with
  | none => simp only [PlayerSpecificAlgebraicComplementaryDraw.draw,FixedArrayTable.read_ofFn]; rfl
  | some pair =>
    obtain ⟨ell,probability⟩ := pair
    simp only [PlayerSpecificAlgebraicTerminalEmbedding.mixed,FixedArrayTable.read_ofFn]
    rfl

theorem random_bit_budget (N H K : ℕ) : bitCount H K ≤ (N+1000)*H+2*K :=
  PlayerSpecificAlgebraicOrderedFourDraw.random_bit_budget N H K

end Blotto.PlayerSpecificAlgebraicTerminalCoreDraw
