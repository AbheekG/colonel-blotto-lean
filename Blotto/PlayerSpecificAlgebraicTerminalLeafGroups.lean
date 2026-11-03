import Blotto.PlayerSpecificAlgebraicLeafBudget

/-! The remaining fractional coordinate is absent from every actual
uniform group, so its direct output write cannot overwrite a group leaf. -/
namespace Blotto.PlayerSpecificAlgebraicTerminalLeafGroups
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicTerminalPreparation PlayerSpecificAlgebraicGrouping
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem member_saturated {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (g : Fin (prepare model p s B).groups.length) (j : Fin N)
    (hj : j ∈ ((prepare model p s B).groups.get g).members) : eval s x j=lengths p x j := by
  have he : j ∈ ((prepare model p s B).groups.map Group.members).flatten :=
    List.mem_flatten.mpr ⟨_,List.mem_map.mpr ⟨_,List.get_mem _ g,rfl⟩,hj⟩
  rw [PlayerSpecificAlgebraicTerminalGroupBounds.members_flatten model p s B x hc,
    uniformItems_value p s x hc.normalized hc.irreducible hc.root.1] at he
  simpa only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq] using he

theorem fractional_not_member {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hend : s.active.length ≤ 1) (k : Fin N)
    (hk : (prepare model p s B).fractional=some k) (g : Fin (prepare model p s B).groups.length) :
    k ∉ ((prepare model p s B).groups.get g).members := by
  have hfr := (fractional_value model p s B x hs hend k).mp hk
  intro hm
  have he : k ∈ ((prepare model p s B).groups.map Group.members).flatten :=
    List.mem_flatten.mpr ⟨_,List.mem_map.mpr ⟨_,List.get_mem _ g,rfl⟩,hm⟩
  rw [PlayerSpecificAlgebraicTerminalGroupBounds.members_flatten model p s B x hc,
    uniformItems_value p s x hc.normalized hc.irreducible hc.root.1] at he
  simp only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq] at he
  exact ne_of_lt hfr.2 he

end Blotto.PlayerSpecificAlgebraicTerminalLeafGroups
