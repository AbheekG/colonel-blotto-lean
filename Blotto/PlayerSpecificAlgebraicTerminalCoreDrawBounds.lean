import Blotto.PlayerSpecificAlgebraicTerminalCoreDraw

/-! Every executed terminal-core output has one absolute linear height
bound, including complement, uniform triple, mixed triple and four-core. -/
namespace Blotto.PlayerSpecificAlgebraicTerminalCoreDrawBounds
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicTerminalCoreInput
open PlayerSpecificAlgebraicTerminalCoreDraw
set_option autoImplicit false
set_option maxHeartbeats 2500000

def height (T K : ℕ) : ℕ := max (PlayerSpecificAlgebraicComplementaryDraw.height T K)
  (max (PlayerSpecificAlgebraicThreeDraw.height (step T) K) (PlayerSpecificAlgebraicOrderedFourDraw.height (step T) K))

def coefficient : ℕ := 4*(PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3+
  (PlayerSpecificAlgebraicThreeDraw.coefficient+PlayerSpecificAlgebraicOrderedFourDraw.coefficient)*
    (PlayerSpecificAlgebraicHeightEnvelope.coefficient+2)

theorem height_linear (T K : ℕ) : height T K+1 ≤ coefficient*(T+K+1) := by
  have hp := PlayerSpecificAlgebraicComplementaryDraw.height_linear T K
  have htf := PlayerSpecificAlgebraicFourSmallDraw.max_linear _ _ _ _ _
    (PlayerSpecificAlgebraicThreeDraw.height_linear (step T) K)
    (PlayerSpecificAlgebraicOrderedFourDraw.height_linear (step T) K)
  have he : step T+K+1 ≤ (PlayerSpecificAlgebraicHeightEnvelope.coefficient+2)*(T+K+1) := by
    dsimp [step]
    nlinarith only [Nat.zero_le T,Nat.zero_le K,Nat.zero_le PlayerSpecificAlgebraicHeightEnvelope.coefficient]
  have ht := htf.trans (Nat.mul_le_mul_left
    (PlayerSpecificAlgebraicThreeDraw.coefficient+PlayerSpecificAlgebraicOrderedFourDraw.coefficient) he)
  have ht' : max (PlayerSpecificAlgebraicThreeDraw.height (step T) K)
      (PlayerSpecificAlgebraicOrderedFourDraw.height (step T) K)+1 ≤
      ((PlayerSpecificAlgebraicThreeDraw.coefficient+PlayerSpecificAlgebraicOrderedFourDraw.coefficient)*
        (PlayerSpecificAlgebraicHeightEnvelope.coefficient+2))*(T+K+1) := by
    simpa only [mul_assoc] using ht
  exact PlayerSpecificAlgebraicFourSmallDraw.max_linear _ _ _ _ _ hp ht'

theorem three_bounds (root : PlayerSpecificAlgebraicCandidates.Candidate) (a : PlayerSpecificAlgebraicThreeInput.Input)
    (T H K : ℕ) (bits : Fin (8*H+K) → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) (hfit : PlayerSpecificAlgebraicThreeEnvironmentSizes.Fits root a T) :
    ∀ j,Reduced root.polynomial ((PlayerSpecificAlgebraicThreeDraw.draw RationalCostModel.schoolbook root a H K bits).read j) ∧
      HasHeight ((PlayerSpecificAlgebraicThreeDraw.draw RationalCostModel.schoolbook root a H K bits).read j)
        (PlayerSpecificAlgebraicThreeDraw.height T K) := by
  intro j
  exact ⟨PlayerSpecificAlgebraicThreeDraw.reduced RationalCostModel.schoolbook root a H K bits hm hm0 j,
    PlayerSpecificAlgebraicThreeDraw.heights RationalCostModel.schoolbook root a H K bits hm hm0 hml T hmT hT hfit j⟩

theorem bounds (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : Valid a x) (T : ℕ) (hfit : PlayerSpecificAlgebraicTerminalCoreFits.Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T)
    (H K : ℕ) (bits : Fin (bitCount H K) → Bool) :
    ∀ j,Reduced r.root.polynomial ((draw r a H K bits).read j) ∧
      HasHeight ((draw r a H K bits).read j) (height T K) := by
  have hm0 : r.root.polynomial ≠ [] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hle : T ≤ step T := (Nat.le_succ _).trans (large T)
  have hfitU := PlayerSpecificAlgebraicTerminalCoreFits.mono r.root a T (step T) hle hfit
  have hmU := PlayerSpecificPolynomialHeights.mono hmT hle
  have hU : 2 ≤ step T := hT.trans hle
  by_cases hc : a.count=2
  · rw [draw,ite_eq_left hc]
    cases hf : a.fractional with
    | none =>
      intro j
      have h := PlayerSpecificAlgebraicComplementaryDraw.bounds r.root a.budget T hm hm0 hml hmT hfit.budget K
        (PlayerSpecificAlgebraicFourSmallDraw.takeBits (midpoint_bit_bound H K) bits) j
      exact ⟨h.1,PlayerSpecificPolynomialHeights.mono h.2 (le_max_left _ _)⟩
    | some pair =>
      obtain ⟨ell,probability⟩ := pair
      have ht := three_bounds r.root (mixedThree a ell probability) (step T) H K
        (PlayerSpecificAlgebraicFourSmallDraw.takeBits (three_bit_bound H K) bits) hm hm0 hml hmU hU
        (PlayerSpecificAlgebraicTerminalCoreFits.mixed_two r.root a (step T) hfitU ell probability hf)
      have he := PlayerSpecificAlgebraicTerminalEmbedding.mixed_bounds r.root _ _ hm0 ht
      intro j
      exact ⟨(he j).1,PlayerSpecificPolynomialHeights.mono (he j).2 ((le_max_left _ _).trans (le_max_right _ _))⟩
  · have hc3 : a.count=3 := ha.count.resolve_left hc
    rw [draw,ite_eq_right hc]
    cases hf : a.fractional with
    | none =>
      have ht := three_bounds r.root (uniformThree r.root a) (step T) H K
        (PlayerSpecificAlgebraicFourSmallDraw.takeBits (three_bit_bound H K) bits) hm hm0 hml hmU hU
        (PlayerSpecificAlgebraicTerminalCoreFits.uniform r.root a T hfit hm hm0 hml hmT (by omega))
      have he := PlayerSpecificAlgebraicTerminalEmbedding.uniform_bounds r.root _ _ hm0 ht
      intro j
      exact ⟨(he j).1,PlayerSpecificPolynomialHeights.mono (he j).2 ((le_max_left _ _).trans (le_max_right _ _))⟩
    | some pair =>
      obtain ⟨ell,probability⟩ := pair
      let i := mixedSpecThree a x ha hc3 ell probability hf
      have h := PlayerSpecificAlgebraicFourSpecDraw.bounds r (mixedFour a ell probability) i.fourInput hm hirr hv x hx
        (mixed_three_values a x ha hc3 ell probability hf) (step T)
        (PlayerSpecificAlgebraicTerminalCoreFits.mixed_three r.root a (step T) hfitU ell probability hf)
        hml hmU hU H K bits
      intro j
      exact ⟨(h j).1,PlayerSpecificPolynomialHeights.mono (h j).2 ((le_max_right _ _).trans (le_max_right _ _))⟩

end Blotto.PlayerSpecificAlgebraicTerminalCoreDrawBounds
