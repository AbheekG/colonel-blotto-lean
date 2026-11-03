import Blotto.PlayerSpecificTerminalCoreReferenceMarginals

/-! Complete marginal error for each used uniform group and the optional
fractional coordinate of the actual terminal core. Unused slots are not
substituted for active groups. -/
namespace Blotto.PlayerSpecificTerminalCoreCDF
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicTerminalCoreInput PlayerSpecificAlgebraicSegment PlayerSpecificTerminalCoreBranchLaws
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def error (H K : ℕ) : ℝ := 80/(2:ℝ)^H+3/(2*(2:ℝ)^K)

theorem three_error (H K : ℕ) : 8/(2:ℝ)^H+1/(2*(2:ℝ)^K) ≤ error H K :=
  add_le_add (div_le_div_of_nonneg_right (by norm_num) (by positivity))
    (div_le_div_of_nonneg_right (by norm_num) (by positivity))

theorem scalar_error (H K : ℕ) : 1/(2*(2:ℝ)^K) ≤ error H K := by
  have h : 1/(2*(2:ℝ)^K) ≤ 3/(2*(2:ℝ)^K) := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  exact h.trans (le_add_of_nonneg_left (by positivity))

theorem uniforms (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : Valid a x) (T : ℕ) (hfit : PlayerSpecificAlgebraicTerminalCoreFits.Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T) (H K : ℕ) :
    ∀ j : Fin 3,j.val < a.count → ∀ z,
      |closedCDF (law r a H K x) j.castSucc z-(uniformLaw (realEvaluate (a.lengths.read j) x)).real (Set.Iic z)| ≤ error H K := by
  by_cases hc : a.count=2
  · cases hf : a.fractional with
    | none =>
      rw [two_none r a H K x hc hf]
      intro j hj z
      let k : Fin 2 := ⟨j.val,by rw [hc] at hj; exact hj⟩
      have hk : k.castSucc.castSucc=j.castSucc := Fin.ext rfl
      have hmarg := PlayerSpecificComplementaryDrawLaw.first_marginals (realEvaluate a.budget x) ha.budget k
      rw [hk] at hmarg
      have hlen := PlayerSpecificTerminalCoreReferenceMarginals.two_none_lengths a x ha hc hf j hj
      have h := ((PlayerSpecificComplementaryDrawLaw.CDF_error r.root a.budget K x hx.1).mono (scalar_error H K)) j.castSucc z
      simpa only [closedCDF,hmarg,hlen] using h
    | some pair =>
      obtain ⟨ell,probability⟩ := pair
      let i := mixedSpecTwo a x ha hc ell probability hf
      have h := PlayerSpecificTerminalEmbeddingLaw.mixed_CDF _ _ _
        (PlayerSpecificThreeDrawLaw.CDF_error RationalCostModel.schoolbook r.root (mixedThree a ell probability)
          i.threeInput H K hm hirr hv x hx (mixed_two_values a x ha hc ell probability hf))
      have hb := h.mono (three_error H K)
      rw [two_some r a H K x hc ell probability hf]
      intro j hj z
      let k : Fin 2 := ⟨j.val,by rw [hc] at hj; exact hj⟩
      have hk : k.castSucc.castSucc=j.castSucc := Fin.ext rfl
      have hk' : k.castSucc=j := Fin.ext rfl
      have hmarg : (marginal (i.threeInput.law.map PlayerSpecificTerminalEmbeddingLaw.mixed) j.castSucc : Measure ℝ)=
          uniformLaw (realEvaluate (a.lengths.read j) x) := by
        rw [←hk,PlayerSpecificTerminalEmbeddingLaw.mixed_first]
        have he := PlayerSpecificTerminalCoreReferenceMarginals.mixed_two_first a x ha hc ell probability hf k
        rw [hk'] at he
        exact he
      simpa only [closedCDF,hmarg] using hb j.castSucc z
  · have hc3 : a.count=3 := ha.count.resolve_left hc
    cases hf : a.fractional with
    | none =>
      let i := uniformSpec a x ha hc3 hf
      have h := PlayerSpecificTerminalEmbeddingLaw.uniform_CDF _ _ _
        (PlayerSpecificThreeDrawLaw.CDF_error RationalCostModel.schoolbook r.root (uniformThree r.root a)
          i.threeInput H K hm hirr hv x hx (uniform_values r.root a x hx.1 ha hc3 hf))
      have hb := h.mono (three_error H K)
      rw [three_none r a H K x hc hf]
      intro j _ z
      have hmarg : (marginal (i.threeInput.law.map PlayerSpecificTerminalEmbeddingLaw.uniform) j.castSucc : Measure ℝ)=
          uniformLaw (realEvaluate (a.lengths.read j) x) := by
        rw [PlayerSpecificTerminalEmbeddingLaw.uniform_marginal]
        exact PlayerSpecificTerminalCoreReferenceMarginals.uniform a x ha hc3 hf j
      simpa only [closedCDF,hmarg] using hb j.castSucc z
    | some pair =>
      obtain ⟨ell,probability⟩ := pair
      let i := mixedSpecThree a x ha hc3 ell probability hf
      have h := PlayerSpecificFourSpecDrawLaw.CDF_error r (mixedFour a ell probability) i.fourInput hm hirr hv x hx
        (mixed_three_values a x ha hc3 ell probability hf) T
        (PlayerSpecificAlgebraicTerminalCoreFits.mixed_three r.root a T hfit ell probability hf) hml hmT hT H K
      rw [three_some r a H K x hc ell probability hf]
      intro j _ z
      have hmarg : (marginal i.fourInput.law j.castSucc : Measure ℝ)=uniformLaw (realEvaluate (a.lengths.read j) x) :=
        PlayerSpecificTerminalCoreReferenceMarginals.mixed_three_first a x ha hc3 ell probability hf j
      simpa only [closedCDF,hmarg,error] using h j.castSucc z

theorem fractional (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : Valid a x) (T : ℕ) (hfit : PlayerSpecificAlgebraicTerminalCoreFits.Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T) (H K : ℕ)
    (ell probability : Data) (hf : a.fractional=some (ell,probability)) (z : ℝ) :
    |closedCDF (law r a H K x) 3 z-(zeroUniformLaw (realEvaluate ell x) (realEvaluate probability x)).real (Set.Iic z)| ≤ error H K := by
  by_cases hc : a.count=2
  · let i := mixedSpecTwo a x ha hc ell probability hf
    have h := PlayerSpecificTerminalEmbeddingLaw.mixed_CDF _ _ _
      (PlayerSpecificThreeDrawLaw.CDF_error RationalCostModel.schoolbook r.root (mixedThree a ell probability)
        i.threeInput H K hm hirr hv x hx (mixed_two_values a x ha hc ell probability hf))
    have hb := h.mono (three_error H K)
    rw [two_some r a H K x hc ell probability hf]
    have hmarg : (marginal (i.threeInput.law.map PlayerSpecificTerminalEmbeddingLaw.mixed) 3 : Measure ℝ)=
        zeroUniformLaw (realEvaluate ell x) (realEvaluate probability x) := by
      rw [PlayerSpecificTerminalEmbeddingLaw.mixed_last]
      exact PlayerSpecificTerminalCoreReferenceMarginals.mixed_two_last a x ha hc ell probability hf
    simpa only [closedCDF,hmarg] using hb 3 z
  · have hc3 : a.count=3 := ha.count.resolve_left hc
    let i := mixedSpecThree a x ha hc3 ell probability hf
    have h := PlayerSpecificFourSpecDrawLaw.CDF_error r (mixedFour a ell probability) i.fourInput hm hirr hv x hx
      (mixed_three_values a x ha hc3 ell probability hf) T
      (PlayerSpecificAlgebraicTerminalCoreFits.mixed_three r.root a T hfit ell probability hf) hml hmT hT H K
    rw [three_some r a H K x hc ell probability hf]
    have hmarg : (marginal i.fourInput.law 3 : Measure ℝ)=zeroUniformLaw (realEvaluate ell x) (realEvaluate probability x) :=
      PlayerSpecificTerminalCoreReferenceMarginals.mixed_three_last a x ha hc3 ell probability hf
    simpa only [closedCDF,hmarg,error] using h 3 z

end Blotto.PlayerSpecificTerminalCoreCDF
