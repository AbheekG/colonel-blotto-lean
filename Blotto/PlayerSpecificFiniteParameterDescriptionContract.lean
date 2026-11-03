import Blotto.PlayerSpecificFiniteParameterDescriptionCost

/-! End-to-end exact finite-bit recognition, concrete portable binary
descriptions, correctness/rejection, accepted algebraic sizes and complete
polynomial source/encoding costs. Bounded equilibrium sampling is separate. -/
namespace Blotto.PlayerSpecificFiniteParameterDescriptionContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction PlayerSpecificFiniteParameterDescription PlayerSpecificFiniteParameterDescriptionCost
open PlayerSpecificFiniteParameterBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem rejection_iff {N : ℕ} (i : RationalPlayerSpecificInput N) :
    (run i).parameters=none ↔ ¬∃ gamma sigma,
      PlayerSpecificRecognition.ValidParameters i.valuesA.values i.valuesB.values (i.budget:ℝ) gamma sigma := by
  rw [value]
  exact PlayerSpecificFiniteParameterReturn.rejection_iff RationalCostModel.schoolbook i

theorem accepted_sound {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (run i).parameters=some r) :
    Normalized r.root.polynomial ∧ Irreducible (semantics r.root.polynomial) ∧ r.root.polynomial.length≤4 ∧
      Reduced r.root.polynomial r.scale ∧
      ∃! x : ℝ,realEvaluate r.root.polynomial x=0 ∧ r.root.interval.Contains x ∧
        PlayerSpecificRecognition.ValidParameters i.valuesA.values i.valuesB.values (i.budget:ℝ) x (realEvaluate r.scale x) :=
  PlayerSpecificFiniteParameterReturn.sound RationalCostModel.schoolbook i r ((value i).symm.trans hr)

theorem accepted_sizes {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (run i).parameters=some r) :
    PlayerSpecificPolynomialHeights.HasHeight r.root.polynomial (height N (inputSize i)) ∧
      RationalHeight r.root.interval.lo (height N (inputSize i)) ∧ RationalHeight r.root.interval.hi (height N (inputSize i)) ∧
      PlayerSpecificPolynomialHeights.HasHeight r.scale (height N (inputSize i)) ∧ r.root.polynomial.length≤4 ∧ r.scale.length≤3 :=
  PlayerSpecificFiniteParameterSizes.actual_sizes RationalCostModel.schoolbook i r ((value i).symm.trans hr)

theorem accepted_equilibrium {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (run i).parameters=some r) :
    ∃ accepted : PlayerSpecificInput N,
      accepted.valuesA=i.valuesA.values ∧ accepted.valuesB=i.valuesB.values ∧ accepted.budget=(i.budget:ℝ) ∧
      realEvaluate r.root.polynomial accepted.gamma=0 ∧ r.root.interval.Contains accepted.gamma ∧
      accepted.scale=realEvaluate r.scale accepted.gamma ∧
      Supported 1 accepted.lawA ∧ Supported (i.budget:ℝ) accepted.lawB ∧
      regret i.valuesA.values 1 accepted.lawA accepted.lawB=0 ∧
      regret i.valuesB.values (i.budget:ℝ) accepted.lawB accepted.lawA=0 :=
  PlayerSpecificFiniteParameterContract.accepted_equilibrium RationalCostModel.schoolbook i r ((value i).symm.trans hr)

theorem actual_contract {N : ℕ} (i : RationalPlayerSpecificInput N) :
    ((run i).parameters=none ↔ ¬∃ gamma sigma,
      PlayerSpecificRecognition.ValidParameters i.valuesA.values i.valuesB.values (i.budget:ℝ) gamma sigma) ∧
      (run i).bits.length≤4*preparationBound N (inputSize i)+3 ∧
      (run i).work≤preparationBound N (inputSize i)+1000*(preparationBound N (inputSize i)+2)^3 ∧
      PlayerSpecificCopyFrame.read (run i).bits=some
        (PlayerSpecificFiniteParameterExecution.frame i (run i).parameters,[]) := by
  have hr:=actual_resources i
  exact ⟨rejection_iff i,hr.1,hr.2.1,hr.2.2⟩

end Blotto.PlayerSpecificFiniteParameterDescriptionContract
