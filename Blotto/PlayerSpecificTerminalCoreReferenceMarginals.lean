import Blotto.PlayerSpecificTerminalCoreBranchLaws

/-! Marginal identities of the exact laws used in the actual terminal
core cases. Every coefficient is the value of its computed input row. -/
namespace Blotto.PlayerSpecificTerminalCoreReferenceMarginals
open MeasureTheory PlayerSpecificSturmVariations PlayerSpecificAlgebraicTerminalCoreInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem two_none_lengths (a : Input) (x : ℝ) (ha : Valid a x) (hc : a.count=2) (hf : a.fractional=none) :
    ∀ j : Fin 3,j.val < a.count → realEvaluate (a.lengths.read j) x=realEvaluate a.budget x := by
  have hs := ha.uniform hf
  rw [sum_two a x hc] at hs
  have h0 := (ha.lengths 0 (by simp [hc])).2
  have h1 := (ha.lengths 1 (by simp [hc])).2
  intro j hj
  fin_cases j
  · change realEvaluate (a.lengths.read 0) x=realEvaluate a.budget x
    linarith only [hs,h0,h1]
  · change realEvaluate (a.lengths.read 1) x=realEvaluate a.budget x
    linarith only [hs,h0,h1]
  · simp only [hc] at hj
    omega

theorem uniform (a : Input) (x : ℝ) (ha : Valid a x) (hc : a.count=3) (hf : a.fractional=none) (j : Fin 3) :
    (marginal (uniformSpec a x ha hc hf).threeInput.law j : Measure ℝ)=uniformLaw (realEvaluate (a.lengths.read j) x) := by
  have h := ((uniformSpec a x ha hc hf).law_contract (Or.inr rfl)).2 j
  exact h

theorem mixed_two_first (a : Input) (x : ℝ) (ha : Valid a x) (hc : a.count=2)
    (ell probability : PlayerSpecificDensePolynomial.Data) (hf : a.fractional=some (ell,probability)) (j : Fin 2) :
    (marginal (mixedSpecTwo a x ha hc ell probability hf).threeInput.law j.castSucc : Measure ℝ)=
      uniformLaw (realEvaluate (a.lengths.read j.castSucc) x) :=
  ((mixedSpecTwo a x ha hc ell probability hf).law_contract (Or.inl rfl)).2.1 j

theorem mixed_two_last (a : Input) (x : ℝ) (ha : Valid a x) (hc : a.count=2)
    (ell probability : PlayerSpecificDensePolynomial.Data) (hf : a.fractional=some (ell,probability)) :
    (marginal (mixedSpecTwo a x ha hc ell probability hf).threeInput.law 2 : Measure ℝ)=
      zeroUniformLaw (realEvaluate ell x) (realEvaluate probability x) :=
  ((mixedSpecTwo a x ha hc ell probability hf).law_contract (Or.inl rfl)).2.2

theorem mixed_three_first (a : Input) (x : ℝ) (ha : Valid a x) (hc : a.count=3)
    (ell probability : PlayerSpecificDensePolynomial.Data) (hf : a.fractional=some (ell,probability)) (j : Fin 3) :
    (marginal (mixedSpecThree a x ha hc ell probability hf).fourInput.law j.castSucc : Measure ℝ)=
      uniformLaw (realEvaluate (a.lengths.read j) x) :=
  (mixedSpecThree a x ha hc ell probability hf).fourInput.law_contract.2.1 j

theorem mixed_three_last (a : Input) (x : ℝ) (ha : Valid a x) (hc : a.count=3)
    (ell probability : PlayerSpecificDensePolynomial.Data) (hf : a.fractional=some (ell,probability)) :
    (marginal (mixedSpecThree a x ha hc ell probability hf).fourInput.law 3 : Measure ℝ)=
      zeroUniformLaw (realEvaluate ell x) (realEvaluate probability x) :=
  (mixedSpecThree a x ha hc ell probability hf).fourInput.law_contract.2.2

end Blotto.PlayerSpecificTerminalCoreReferenceMarginals
