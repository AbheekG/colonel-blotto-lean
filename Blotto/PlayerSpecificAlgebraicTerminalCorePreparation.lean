import Blotto.PlayerSpecificAlgebraicTerminalCoreValues

/-! Reached resource invariants imply all actual group-core promises.
No partition, probability, branch or size oracle is supplied to the code. -/
namespace Blotto.PlayerSpecificAlgebraicTerminalCorePreparation
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicTerminalPreparation
open PlayerSpecificAlgebraicTerminalCoreValues
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem valid {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0 < B) (hL : ∀ k,0 < lengths p x k ∧ lengths p x k ≤ B)
    (hb : InBox (lengths p x) (eval s x)) (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length ≤ 1)
    (H : ℕ) (hsize : ∀ k,HasHeight (p.rows.read k).length H) :
    PlayerSpecificAlgebraicTerminalCoreInput.Valid
      (PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B (prepare model p s B)) x := by
  let g := prepare model p s B
  let a := PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B g
  let t := interpret p s B x hs hB hL hb hmass hend
  have hcount := groups_count model p s B x hc hs hB hL hb hmass hend
  have hcached := PlayerSpecificAlgebraicTerminalGroupBounds.cached_bounds model p s B x hc hs hB hL hb hmass hend H hsize
  have hsum : PlayerSpecificAlgebraicTerminalCoreInput.groupSum a x=t.uniformMass :=
    (prepared_sum p s B g x hcount.2).trans (cached_mass model p s B x hc hs hB hL hb hmass hend)
  have hbudget : realEvaluate a.budget x=(B:ℝ) := PlayerSpecificAlgebraicField.constant_value _ B x hc.root.1
  refine ⟨?_,?_,?_,?_,?_⟩
  · change g.groups.length=2 ∨ g.groups.length=3
    change 2 ≤ g.groups.length ∧ g.groups.length ≤ 3 at hcount
    omega
  · rw [hbudget]
    exact_mod_cast hB
  · intro j hj
    change j.val < g.groups.length at hj
    rw [length_read p s B g j hj,hbudget]
    have hg := hcached (g.groups[j.val]) (List.getElem_mem hj)
    exact ⟨hg.2.2.2.1,hg.2.2.2.2.1⟩
  · intro hnone
    have hn : g.fractional=none := by
      change (g.fractional.map _)=none at hnone
      exact Option.map_eq_none_iff.mp hnone
    have hfr : ∀ j,¬Fractional t.length t.resource j := by
      intro j hj
      have he := (fractional_value model p s B x hs hend j).mpr hj
      rw [hn] at he
      cases he
    rw [hsum,hbudget]
    exact t.uniformMass_no_fraction hfr
  · intro ell probability hsome
    change (g.fractional.map _)=some (ell,probability) at hsome
    obtain ⟨k,hk,hpair⟩ := Option.map_eq_some_iff.mp hsome
    have he : (p.rows.read k).length=ell := congrArg Prod.fst hpair
    have hq : PlayerSpecificAlgebraicField.divide p.parameters.root.polynomial (s.data.read k) (p.rows.read k).length=probability := congrArg Prod.snd hpair
    rw [← he,← hq]
    have hfr := (fractional_value model p s B x hs hend k).mp hk
    have hdiv := PlayerSpecificAlgebraicField.divide_value p.parameters.root.polynomial (s.data.read k) (p.rows.read k).length hc.normalized hc.irreducible
      (hc.lengths k) x hc.root.1
    change 0 < lengths p x k ∧ lengths p x k ≤ realEvaluate a.budget x ∧
      0 < realEvaluate (PlayerSpecificAlgebraicField.divide p.parameters.root.polynomial (s.data.read k) (p.rows.read k).length) x ∧
      realEvaluate (PlayerSpecificAlgebraicField.divide p.parameters.root.polynomial (s.data.read k) (p.rows.read k).length) x < 1 ∧ _
    rw [hdiv,hbudget]
    refine ⟨(hL k).1,(hL k).2,div_pos hfr.1 (hL k).1,(div_lt_one (hL k).1).mpr hfr.2,?_⟩
    rw [hsum]
    change t.uniformMass+eval s x k/lengths p x k*lengths p x k=2*(B:ℝ)
    rw [div_mul_cancel₀ _ (ne_of_gt (hL k).1)]
    exact t.uniformMass_with_fraction k hfr

end Blotto.PlayerSpecificAlgebraicTerminalCorePreparation
