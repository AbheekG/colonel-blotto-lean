import Blotto.PlayerSpecificFiniteParameterCopyCost

/-! Complete original-input source time for the actual finite-bit parameter
recognizer, including accepted scale and all enclosing description copies.
Every stage bound is derived from executed input and returned records. -/
namespace Blotto.PlayerSpecificFiniteParameterCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificFiniteParameterBudget PlayerSpecificFiniteParameterStages
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem run_eq {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    PlayerSpecificFiniteParameterExecution.run model i=
      match (selected model i).1 with
      | none => (none,(prepared model i).2+(selected model i).2+price model (PlayerSpecificFiniteParameterExecution.frame i none))
      | some chosen =>
        let result:PlayerSpecificFiniteParameterReturn.Result:=⟨chosen.1,chosen.2,(scale model i chosen).1⟩
        (some result,(prepared model i).2+(selected model i).2+(scale model i chosen).2+
          price model (PlayerSpecificFiniteParameterExecution.frame i (some result))) := rfl

theorem caller_price_le {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) (extra : ℕ)
    (hn : price model (PlayerSpecificFiniteParameterExecution.frame i none)≤extra)
    (ha : ∀ chosen,(selected model i).1=some chosen →
      (scale model i chosen).2+price model (PlayerSpecificFiniteParameterExecution.frame i
        (some ⟨chosen.1,chosen.2,(scale model i chosen).1⟩))≤(selected model i).2+extra) :
    (PlayerSpecificFiniteParameterExecution.run model i).2≤(prepared model i).2+2*(selected model i).2+extra := by
  rw [run_eq]
  cases hr : (selected model i).1 with
  | none => simpa only [hr] using (by omega :
      (prepared model i).2+(selected model i).2+price model (PlayerSpecificFiniteParameterExecution.frame i none)≤
        (prepared model i).2+2*(selected model i).2+extra)
  | some chosen =>
    have hc:=ha chosen hr
    simpa only [hr] using (by omega :
      (prepared model i).2+(selected model i).2+(scale model i chosen).2+
        price model (PlayerSpecificFiniteParameterExecution.frame i (some ⟨chosen.1,chosen.2,(scale model i chosen).1⟩))≤
        (prepared model i).2+2*(selected model i).2+extra)

theorem accepted_extra {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N)
    (chosen : PlayerSpecificRationalCells.Cell×PlayerSpecificAlgebraicCandidates.Candidate)
    (hr : (selected model i).1=some chosen) :
    (scale model i chosen).2+price model (PlayerSpecificFiniteParameterExecution.frame i
      (some ⟨chosen.1,chosen.2,(scale model i chosen).1⟩))≤
      (selected model i).2+(1000000000+1000)*work N (inputSize i)*model.rat (width N (inputSize i)) := by
  have hc:=(accepted_scale model i chosen hr).2.2
  have hm:=Nat.mul_le_mul_right (1000000000*model.rat (width N (inputSize i))) (work_profiles N (inputSize i)).2.2.2
  have hf:=PlayerSpecificFiniteParameterCopyCost.accepted_frame model i chosen hr
  nlinarith only [hc,hm,hf]

theorem bound_profile (A B C T R prepared selected : ℕ) (hp : prepared≤A*T*R) (hs : selected≤B*T*R) :
    prepared+2*selected+C*T*R≤(A+2*B+C)*T*R := by nlinarith only [hp,hs]

theorem coefficient_formula : 10000000+2*PlayerSpecificRecognitionScanContract.workCoefficient+(1000000000+1000)=workCoefficient := by
  unfold workCoefficient
  omega

theorem source_cost {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    (PlayerSpecificFiniteParameterExecution.run model i).2≤workCoefficient*work N (inputSize i)*
      model.rat (width N (inputSize i)) := by
  have hp:=preparation_cost model i
  have hs:=scan_cost model i
  have hn:=PlayerSpecificFiniteParameterCopyCost.none_frame model i
  have hnp : price model (PlayerSpecificFiniteParameterExecution.frame i none)≤
      (1000000000+1000)*work N (inputSize i)*model.rat (width N (inputSize i)) := by
    exact hn.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 1000≤1000000000+1000)))
  have hc:=caller_price_le model i _ hnp (accepted_extra model i)
  have hb:=bound_profile 10000000 PlayerSpecificRecognitionScanContract.workCoefficient (1000000000+1000)
    (work N (inputSize i)) (model.rat (width N (inputSize i))) _ _ hp hs
  rw [coefficient_formula] at hb
  exact hc.trans hb

theorem schoolbook_profile (C D T S : ℕ) (hS : 1≤S) :
    C*T*RationalCostModel.schoolbook.rat (D*S)≤(C*(D*D+D))*T*S^2 := by
  have hp:=PlayerSpecificAlgebraicInverseContract.quadratic_profile C D S hS
  have hm:=Nat.mul_le_mul_left T hp
  dsimp only [RationalCostModel.schoolbook]
  ring_nf at hm ⊢
  exact hm

theorem polynomial_cost {N : ℕ} (i : RationalPlayerSpecificInput N) :
    (PlayerSpecificFiniteParameterExecution.run RationalCostModel.schoolbook i).2≤
      (workCoefficient*(widthCoefficient*widthCoefficient+widthCoefficient))*work N (inputSize i)*size N (inputSize i)^2 :=
  (source_cost RationalCostModel.schoolbook i).trans
    (schoolbook_profile workCoefficient widthCoefficient (work N (inputSize i)) (size N (inputSize i)) (size_positive N (inputSize i)))

end Blotto.PlayerSpecificFiniteParameterCost
