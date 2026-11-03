import Blotto.PlayerSpecificComplementaryDrawLaw
import Blotto.PlayerSpecificFourSpecDrawLaw
import Blotto.PlayerSpecificAlgebraicTerminalCoreDraw

/-! Exact law identities for all four executing terminal core layouts.
They include native embedding, fixed packet reservation and unused bits. -/
namespace Blotto.PlayerSpecificTerminalCoreBranchLaws
open MeasureTheory PlayerSpecificSturmVariations PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicTerminalCoreInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def law (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ) (x : ℝ) : Mixed 4 :=
  (fairBitLaw (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K)).map
    (fun bits => values (PlayerSpecificAlgebraicTerminalCoreDraw.draw r a H K bits) x)

theorem two_none (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ) (x : ℝ)
    (hc : a.count=2) (hf : a.fractional=none) :
    law r a H K x=PlayerSpecificComplementaryDrawLaw.law r.root a.budget K x := by
  have he : (fun bits => values (PlayerSpecificAlgebraicTerminalCoreDraw.draw r a H K bits) x)=
      (fun bits => values (PlayerSpecificAlgebraicComplementaryDraw.draw r.root a.budget K
        (PlayerSpecificAlgebraicFourSmallDraw.takeBits (PlayerSpecificAlgebraicTerminalCoreDraw.midpoint_bit_bound H K) bits)) x) := by
    funext bits
    rw [PlayerSpecificAlgebraicTerminalCoreDraw.draw,ite_eq_left hc,hf]
  unfold law
  rw [he,PlayerSpecificFairPrefix.law K _ (PlayerSpecificAlgebraicTerminalCoreDraw.midpoint_bit_bound H K)
    (fun bits => values (PlayerSpecificAlgebraicComplementaryDraw.draw r.root a.budget K bits) x)]
  rfl

theorem two_some (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ) (x : ℝ)
    (hc : a.count=2) (ell probability : PlayerSpecificDensePolynomial.Data) (hf : a.fractional=some (ell,probability)) :
    law r a H K x=(PlayerSpecificThreeDrawLaw.law RationalCostModel.schoolbook r.root (mixedThree a ell probability) H K x).map
      PlayerSpecificTerminalEmbeddingLaw.mixed := by
  have he : (fun bits => values (PlayerSpecificAlgebraicTerminalCoreDraw.draw r a H K bits) x)=
      (fun bits => PlayerSpecificTerminalEmbeddingLaw.mixed (values (PlayerSpecificAlgebraicThreeDraw.draw
        RationalCostModel.schoolbook r.root (mixedThree a ell probability) H K
        (PlayerSpecificAlgebraicFourSmallDraw.takeBits (PlayerSpecificAlgebraicTerminalCoreDraw.three_bit_bound H K) bits)) x)) := by
    funext bits
    rw [PlayerSpecificAlgebraicTerminalCoreDraw.draw,ite_eq_left hc,hf,PlayerSpecificAlgebraicTerminalEmbedding.mixed_value]
    rfl
  unfold law
  rw [he,PlayerSpecificFairPrefix.law (8*H+K) _ (PlayerSpecificAlgebraicTerminalCoreDraw.three_bit_bound H K)
    (fun bits => PlayerSpecificTerminalEmbeddingLaw.mixed (values (PlayerSpecificAlgebraicThreeDraw.draw
      RationalCostModel.schoolbook r.root (mixedThree a ell probability) H K bits) x))]
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map _ _=Measure.map PlayerSpecificTerminalEmbeddingLaw.mixed (Measure.map _ _)
  rw [Measure.map_map PlayerSpecificTerminalEmbeddingLaw.measurable_mixed (measurable_of_countable _)]
  rfl

theorem three_none (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ) (x : ℝ)
    (hc : a.count≠2) (hf : a.fractional=none) :
    law r a H K x=(PlayerSpecificThreeDrawLaw.law RationalCostModel.schoolbook r.root (uniformThree r.root a) H K x).map
      PlayerSpecificTerminalEmbeddingLaw.uniform := by
  have he : (fun bits => values (PlayerSpecificAlgebraicTerminalCoreDraw.draw r a H K bits) x)=
      (fun bits => PlayerSpecificTerminalEmbeddingLaw.uniform (values (PlayerSpecificAlgebraicThreeDraw.draw
        RationalCostModel.schoolbook r.root (uniformThree r.root a) H K
        (PlayerSpecificAlgebraicFourSmallDraw.takeBits (PlayerSpecificAlgebraicTerminalCoreDraw.three_bit_bound H K) bits)) x)) := by
    funext bits
    rw [PlayerSpecificAlgebraicTerminalCoreDraw.draw,ite_eq_right hc,hf,PlayerSpecificAlgebraicTerminalEmbedding.uniform_value]
    rfl
  unfold law
  rw [he,PlayerSpecificFairPrefix.law (8*H+K) _ (PlayerSpecificAlgebraicTerminalCoreDraw.three_bit_bound H K)
    (fun bits => PlayerSpecificTerminalEmbeddingLaw.uniform (values (PlayerSpecificAlgebraicThreeDraw.draw
      RationalCostModel.schoolbook r.root (uniformThree r.root a) H K bits) x))]
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map _ _=Measure.map PlayerSpecificTerminalEmbeddingLaw.uniform (Measure.map _ _)
  rw [Measure.map_map PlayerSpecificTerminalEmbeddingLaw.measurable_uniform (measurable_of_countable _)]
  rfl

theorem three_some (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ) (x : ℝ)
    (hc : a.count≠2) (ell probability : PlayerSpecificDensePolynomial.Data) (hf : a.fractional=some (ell,probability)) :
    law r a H K x=PlayerSpecificFourSpecDrawLaw.law r (mixedFour a ell probability) H K x := by
  have he : (fun bits => values (PlayerSpecificAlgebraicTerminalCoreDraw.draw r a H K bits) x)=
      (fun bits => values (PlayerSpecificAlgebraicFourSpecDraw.draw r (mixedFour a ell probability) H K bits) x) := by
    funext bits
    rw [PlayerSpecificAlgebraicTerminalCoreDraw.draw,ite_eq_right hc,hf]
  unfold law
  rw [he]
  rfl

end Blotto.PlayerSpecificTerminalCoreBranchLaws
