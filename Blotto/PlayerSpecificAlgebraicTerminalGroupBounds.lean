import Blotto.PlayerSpecificAlgebraicTerminalPreparation

/-! Cached terminal group members form the exact disjoint partition of
uniform coordinates. Group totals are positive, capped and bounded by
the original nonrepeating endpoint leaves. -/
namespace Blotto.PlayerSpecificAlgebraicTerminalGroupBounds
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicGrouping
open PlayerSpecificAlgebraicGroupingCache PlayerSpecificAlgebraicTerminalPreparation
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem members_flatten {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) :
    ((prepare model p s B).groups.map Group.members).flatten=uniformItems p s := by
  rw [prepare,PlayerSpecificAlgebraicGrouping.members model p.parameters.root _ B _ hc.normalized hc.irreducible hc.interval x hc.root,
    greedyGroups_flatten]

theorem members_nodup {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) :
    ((prepare model p s B).groups.map Group.members).flatten.Nodup := by
  rw [members_flatten model p s B x hc]
  exact (List.nodup_finRange N).filter _

theorem cached_bounds {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0<B) (hL : ∀ k,0<lengths p x k ∧ lengths p x k≤B)
    (hb : InBox (lengths p x) (eval s x)) (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length≤1)
    (H : ℕ) (hsize : ∀ k,HasHeight (p.rows.read k).length H) :
    ∀ g∈(prepare model p s B).groups,
      g.members.Nodup ∧ g.members≠[] ∧ Reduced p.parameters.root.polynomial g.total ∧
      0<realEvaluate g.total x ∧ realEvaluate g.total x≤B ∧ HasHeight g.total ((H+1)*(N+N)+3) := by
  have hm0 : p.parameters.root.polynomial≠[] := by intro hz; exact hc.irreducible.ne_zero (by rw [hz]; rfl)
  have hcache:=groups_cached model p s B hc.normalized hm0 hc.lengths
  have hn:=members_nodup model p s B x hc
  have he:=groups_value model p s B x hc hs hB hL hb hmass hend
  let t:=interpret p s B x hs hB hL hb hmass hend
  intro g hg
  have hmem : g.members∈(prepare model p s B).groups.map Group.members := List.mem_map.mpr ⟨g,hg,rfl⟩
  have hgn:= (List.nodup_flatten.mp hn).1 _ hmem
  have htg : g.members∈t.groups := he ▸ hmem
  have hbound:=t.groups_bounds _ htg
  have hval:=cache_value p.parameters.root _ g (hcache g hg) x
  refine ⟨hgn,hbound.1,(hcache g hg).1,?_,?_,?_⟩
  · rw [hval]; exact hbound.2.1
  · rw [hval]; exact hbound.2.2
  · exact cache_height p.parameters.root _ g (hcache g hg) hc.normalized hm0 H (fun k => ⟨hc.lengths k,hsize k⟩) hgn

end Blotto.PlayerSpecificAlgebraicTerminalGroupBounds
