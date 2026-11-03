import Blotto.PlayerSpecificFiniteParameterReturn

/-! Same-return exact finite-bit parameter soundness and rejection. The
accepted algebraic representation also entails the checked exact equilibrium
laws; the bounded finite-bit sampling implementation remains separate. -/
namespace Blotto.PlayerSpecificFiniteParameterContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction PlayerSpecificFiniteParameterReturn
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem actual_contract {n : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput n) :
    (run model i=none ↔ ¬∃ gamma sigma,
      PlayerSpecificRecognition.ValidParameters i.valuesA.values i.valuesB.values (i.budget:ℝ) gamma sigma) ∧
    ∀ r,run model i=some r →
      Normalized r.root.polynomial ∧ Irreducible (semantics r.root.polynomial) ∧ r.root.polynomial.length≤4 ∧
        Reduced r.root.polynomial r.scale ∧
        ∃! x : ℝ,realEvaluate r.root.polynomial x=0 ∧ r.root.interval.Contains x ∧
          PlayerSpecificRecognition.ValidParameters i.valuesA.values i.valuesB.values (i.budget:ℝ) x (realEvaluate r.scale x) :=
  ⟨rejection_iff model i,fun r hr => sound model i r hr⟩

theorem accepted_equilibrium {n : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput n) (r : Result)
    (hr : run model i=some r) :
    ∃ accepted : PlayerSpecificInput n,
      accepted.valuesA=i.valuesA.values ∧ accepted.valuesB=i.valuesB.values ∧ accepted.budget=(i.budget:ℝ) ∧
      realEvaluate r.root.polynomial accepted.gamma=0 ∧ r.root.interval.Contains accepted.gamma ∧
      accepted.scale=realEvaluate r.scale accepted.gamma ∧
      Supported 1 accepted.lawA ∧ Supported (i.budget:ℝ) accepted.lawB ∧
      regret i.valuesA.values 1 accepted.lawA accepted.lawB=0 ∧
      regret i.valuesB.values (i.budget:ℝ) accepted.lawB accepted.lawA=0 := by
  obtain ⟨x,hx,_⟩:=(sound model i r hr).2.2.2.2
  let accepted:=PlayerSpecificRecognition.toInput i.valuesA.values i.valuesB.values (i.budget:ℝ) x (realEvaluate r.scale x)
    (by exact_mod_cast i.budget_pos) (by exact_mod_cast i.budget_le) hx.2.2
  have hn:=PlayerSpecificEquilibrium.exact_nash accepted
  exact ⟨accepted,rfl,rfl,rfl,hx.1,hx.2.1,rfl,accepted.lawA_supported,accepted.lawB_supported,hn.1,hn.2.1⟩

end Blotto.PlayerSpecificFiniteParameterContract
