import Blotto.PlayerSpecificAlgebraicTerminalCoreInput

/-! The actual cached group array has the exact reached uniform mass.
Only the first two/three slots contribute; its optional quotient retains
the original fractional coordinate. -/
namespace Blotto.PlayerSpecificAlgebraicTerminalCoreValues
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicGrouping PlayerSpecificAlgebraicGroupingCache
open PlayerSpecificAlgebraicTerminalPreparation
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem length_read {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (B : ℚ)
    (g : Prepared N) (j : Fin 3) (hj : j.val < g.groups.length) :
    ((PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B g).lengths.read j)=g.groups[j.val].total := by
  simp only [PlayerSpecificAlgebraicTerminalCoreInput.prepare,FixedArrayTable.read_ofFn,
    List.getElem?_eq_getElem hj,Option.map_some,Option.getD_some]

theorem prepared_sum {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (B : ℚ)
    (g : Prepared N) (x : ℝ) (h : g.groups.length ≤ 3) :
    PlayerSpecificAlgebraicTerminalCoreInput.groupSum (PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B g) x=
      (g.groups.map (fun a => realEvaluate a.total x)).sum := by
  cases hg : g.groups with
  | nil => simp [PlayerSpecificAlgebraicTerminalCoreInput.prepare,PlayerSpecificAlgebraicTerminalCoreInput.groupSum,hg]
  | cons a rest =>
    cases rest with
    | nil => simp [PlayerSpecificAlgebraicTerminalCoreInput.prepare,PlayerSpecificAlgebraicTerminalCoreInput.groupSum,hg,FixedArrayTable.read_ofFn]
    | cons b rest =>
      cases rest with
      | nil => simp [PlayerSpecificAlgebraicTerminalCoreInput.prepare,PlayerSpecificAlgebraicTerminalCoreInput.groupSum,hg,FixedArrayTable.read_ofFn,Fin.sum_univ_succ]
      | cons c rest =>
        cases rest with
        | nil => simp [PlayerSpecificAlgebraicTerminalCoreInput.prepare,PlayerSpecificAlgebraicTerminalCoreInput.groupSum,hg,FixedArrayTable.read_ofFn,Fin.sum_univ_succ]
        | cons d rest => simp only [hg,List.length_cons] at h; omega

theorem cached_mass {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0 < B) (hL : ∀ k,0 < lengths p x k ∧ lengths p x k ≤ B)
    (hb : InBox (lengths p x) (eval s x)) (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length ≤ 1) :
    ((prepare model p s B).groups.map (fun g => realEvaluate g.total x)).sum=
      (interpret p s B x hs hB hL hb hmass hend).uniformMass := by
  have hm0 : p.parameters.root.polynomial ≠ [] := by intro hz; exact hc.irreducible.ne_zero (by rw [hz]; rfl)
  have hcache := groups_cached model p s B hc.normalized hm0 hc.lengths
  have hg := groups_value model p s B x hc hs hB hL hb hmass hend
  have hmap : (prepare model p s B).groups.map (fun g => realEvaluate g.total x)=
      ((prepare model p s B).groups.map Group.members).map (groupLength (lengths p x)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro g hmem
    exact cache_value p.parameters.root _ g (hcache g hmem) x
  rw [hmap,hg]
  exact (interpret p s B x hs hB hL hb hmass hend).groups_mass

end Blotto.PlayerSpecificAlgebraicTerminalCoreValues
