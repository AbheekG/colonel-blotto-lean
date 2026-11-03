import Blotto.PlayerSpecificHybridLimit

/-! Every actual terminal core has an H-independent finite-midpoint
exact-choice hybrid with whole-event error at most 80*2^-H. -/
namespace Blotto.PlayerSpecificTerminalCoreHybrid
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicTerminalCoreInput PlayerSpecificTerminalCoreBranchLaws
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem exists_hybrid (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : Valid a x) (T : ℕ) (hfit : PlayerSpecificAlgebraicTerminalCoreFits.Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T) (K : ℕ) :
    ∃ hybrid : Mixed 4,∀ H,PlayerSpecificEventDistance.Bound (law r a H K x) hybrid (80/(2:ℝ)^H) := by
  by_cases hc : a.count=2
  · cases hf : a.fractional with
    | none =>
      refine ⟨PlayerSpecificComplementaryDrawLaw.law r.root a.budget K x,?_⟩
      intro H
      rw [two_none r a H K x hc hf]
      intro A _
      simp only [sub_self,abs_zero]
      positivity
    | some pair =>
      obtain ⟨ell,probability⟩ := pair
      let i := mixedSpecTwo a x ha hc ell probability hf
      refine ⟨(i.threeInput.segmentLottery.dyadicLaw K).map PlayerSpecificTerminalEmbeddingLaw.mixed,?_⟩
      intro H
      have h : PlayerSpecificEventDistance.Bound (PlayerSpecificThreeDrawLaw.law RationalCostModel.schoolbook r.root
          (mixedThree a ell probability) H K x) (i.threeInput.segmentLottery.dyadicLaw K) (8/(2:ℝ)^H) :=
        fun A hA => PlayerSpecificThreeDrawLaw.event_error RationalCostModel.schoolbook r.root (mixedThree a ell probability)
          i.threeInput H K hm hirr hv x hx (mixed_two_values a x ha hc ell probability hf) A hA
      rw [two_some r a H K x hc ell probability hf]
      exact PlayerSpecificEventDistance.mono _ _ _ _ (PlayerSpecificEventDistance.map _ _ _ h
        PlayerSpecificTerminalEmbeddingLaw.mixed PlayerSpecificTerminalEmbeddingLaw.measurable_mixed)
        (div_le_div_of_nonneg_right (by norm_num) (by positivity))
  · have hc3 : a.count=3 := ha.count.resolve_left hc
    cases hf : a.fractional with
    | none =>
      let i := uniformSpec a x ha hc3 hf
      refine ⟨(i.threeInput.segmentLottery.dyadicLaw K).map PlayerSpecificTerminalEmbeddingLaw.uniform,?_⟩
      intro H
      have h : PlayerSpecificEventDistance.Bound (PlayerSpecificThreeDrawLaw.law RationalCostModel.schoolbook r.root
          (uniformThree r.root a) H K x) (i.threeInput.segmentLottery.dyadicLaw K) (8/(2:ℝ)^H) :=
        fun A hA => PlayerSpecificThreeDrawLaw.event_error RationalCostModel.schoolbook r.root (uniformThree r.root a)
          i.threeInput H K hm hirr hv x hx (uniform_values r.root a x hx.1 ha hc3 hf) A hA
      rw [three_none r a H K x hc hf]
      exact PlayerSpecificEventDistance.mono _ _ _ _ (PlayerSpecificEventDistance.map _ _ _ h
        PlayerSpecificTerminalEmbeddingLaw.uniform PlayerSpecificTerminalEmbeddingLaw.measurable_uniform)
        (div_le_div_of_nonneg_right (by norm_num) (by positivity))
    | some pair =>
      obtain ⟨ell,probability⟩ := pair
      let i := mixedSpecThree a x ha hc3 ell probability hf
      obtain ⟨hybrid,hevent,_⟩ := PlayerSpecificFourSpecHybrid.exists_hybrid r (mixedFour a ell probability) i.fourInput
        hm hirr hv x hx (mixed_three_values a x ha hc3 ell probability hf) T
        (PlayerSpecificAlgebraicTerminalCoreFits.mixed_three r.root a T hfit ell probability hf) hml hmT hT K
      refine ⟨hybrid,?_⟩
      intro H
      rw [three_some r a H K x hc ell probability hf]
      exact hevent H

end Blotto.PlayerSpecificTerminalCoreHybrid
