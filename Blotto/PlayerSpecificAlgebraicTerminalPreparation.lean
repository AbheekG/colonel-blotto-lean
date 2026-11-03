import Blotto.PlayerSpecificAlgebraicGroupingCache

/-! Executable terminal group preparation and proof-only interpretation.
The return retains two or three uniform groups and the optional remaining
fractional coordinate, with every group total cached exactly once. -/
namespace Blotto.PlayerSpecificAlgebraicTerminalPreparation
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicGrouping
open PlayerSpecificAlgebraicGroupingCache
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Prepared (N : ℕ) where
  groups : List (Group N)
  fractional : Option (Fin N)

def prepare {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) : Prepared N :=
  ⟨PlayerSpecificAlgebraicGrouping.run model p.parameters.root (fun k => (p.rows.read k).length) B (uniformItems p s),s.active.head?⟩

noncomputable def interpret {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (B : ℚ) (x : ℝ)
    (hs : Valid p x s) (hB : 0<B) (hL : ∀ k,0<lengths p x k ∧ lengths p x k≤B)
    (hb : InBox (lengths p x) (eval s x)) (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length≤1) : TerminalLotto N where
  B := B
  length := lengths p x
  resource := eval s x
  B_pos := by exact_mod_cast hB
  length_pos := fun k => (hL k).1
  length_le := fun k => (hL k).2
  box := hb
  resource_sum := hmass
  fractional_le := by rw [←length_eq_card p x s hs]; exact hend

theorem groups_value {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0<B) (hL : ∀ k,0<lengths p x k ∧ lengths p x k≤B)
    (hb : InBox (lengths p x) (eval s x)) (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length≤1) :
    ((prepare model p s B).groups.map Group.members)=(interpret p s B x hs hB hL hb hmass hend).groups := by
  rw [prepare,PlayerSpecificAlgebraicGrouping.members model p.parameters.root _ B _ hc.normalized hc.irreducible hc.interval x hc.root,
    uniformItems_value p s x hc.normalized hc.irreducible hc.root.1]
  rfl

theorem groups_count {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0<B) (hL : ∀ k,0<lengths p x k ∧ lengths p x k≤B)
    (hb : InBox (lengths p x) (eval s x)) (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length≤1) :
    2≤(prepare model p s B).groups.length ∧ (prepare model p s B).groups.length≤3 := by
  have he:=congrArg List.length (groups_value model p s B x hc hs hB hL hb hmass hend)
  simp only [List.length_map] at he
  let t:=interpret p s B x hs hB hL hb hmass hend
  exact ⟨he.symm ▸ t.groups_count_lower,he.symm ▸ t.groups_count_upper⟩

theorem fractional_value {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hs : Valid p x s) (hend : s.active.length≤1) (k : Fin N) :
    (prepare model p s B).fractional=some k ↔ Fractional (lengths p x) (eval s x) k := by
  rw [←hs.membership k]
  change s.active.head?=some k ↔ k∈s.active
  cases he : s.active with
  | nil => simp
  | cons j tail =>
      have htail : tail=[] := List.length_eq_zero_iff.mp (by rw [he,List.length_cons] at hend; omega)
      simp only [htail,List.head?_cons,Option.some.injEq,List.mem_singleton,eq_comm]

theorem groups_cached {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (hm : Normalized p.parameters.root.polynomial) (hm0 : p.parameters.root.polynomial≠[])
    (hL : ∀ k,Reduced p.parameters.root.polynomial (p.rows.read k).length) :
    ∀ g∈(prepare model p s B).groups,Cache p.parameters.root (fun k => (p.rows.read k).length) g :=
  cache model p.parameters.root _ B (uniformItems p s) hm hm0 hL

end Blotto.PlayerSpecificAlgebraicTerminalPreparation
