import Blotto.PlayerSpecificAlgebraicTerminalCorePreparation

/-! Stored terminal-core sizes transfer to each computed raw core input.
The extra constant-one layer is charged uniformly to all dispatch cases. -/
namespace Blotto.PlayerSpecificAlgebraicTerminalCoreFits
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicTerminalCoreInput
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Fits (root : Candidate) (a : Input) (T : ℕ) : Prop where
  budget : Reduced root.polynomial a.budget ∧ HasHeight a.budget T
  lengths : ∀ j,Reduced root.polynomial (a.lengths.read j) ∧ HasHeight (a.lengths.read j) T
  fractional : ∀ ell probability,a.fractional=some (ell,probability) →
    (Reduced root.polynomial ell ∧ HasHeight ell T) ∧
      (Reduced root.polynomial probability ∧ HasHeight probability T)

theorem mono (root : Candidate) (a : Input) (T U : ℕ) (h : T ≤ U) (ha : Fits root a T) : Fits root a U := by
  refine ⟨⟨ha.budget.1,PlayerSpecificPolynomialHeights.mono ha.budget.2 h⟩,?_,?_⟩
  · intro j
    exact ⟨(ha.lengths j).1,PlayerSpecificPolynomialHeights.mono (ha.lengths j).2 h⟩
  · intro ell probability hf
    have hp := ha.fractional ell probability hf
    exact ⟨⟨hp.1.1,PlayerSpecificPolynomialHeights.mono hp.1.2 h⟩,
      ⟨hp.2.1,PlayerSpecificPolynomialHeights.mono hp.2.2 h⟩⟩

theorem uniform (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 1 ≤ T) :
    PlayerSpecificAlgebraicThreeEnvironmentSizes.Fits root (uniformThree root a) (step T) := by
  have hle : T ≤ step T := (Nat.le_succ _).trans (large T)
  have hf := mono root a T (step T) hle ha
  exact ⟨hf.budget,hf.lengths 0,hf.lengths 1,hf.lengths 2,
    PlayerSpecificAlgebraicField.constant_reduced _ 1 hm hm0,
    constant_height _ 1 T hmT (one_height.mono hT) hT hml⟩

theorem mixed_two (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T)
    (ell probability : Data) (hf : a.fractional=some (ell,probability)) :
    PlayerSpecificAlgebraicThreeEnvironmentSizes.Fits root (mixedThree a ell probability) T :=
  ⟨ha.budget,ha.lengths 0,ha.lengths 1,(ha.fractional ell probability hf).1,(ha.fractional ell probability hf).2⟩

theorem mixed_three (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T)
    (ell probability : Data) (hf : a.fractional=some (ell,probability)) :
    PlayerSpecificAlgebraicFourSpecInput.Fits root (mixedFour a ell probability) T :=
  ⟨ha.budget,ha.lengths,(ha.fractional ell probability hf).1,(ha.fractional ell probability hf).2⟩

end Blotto.PlayerSpecificAlgebraicTerminalCoreFits
