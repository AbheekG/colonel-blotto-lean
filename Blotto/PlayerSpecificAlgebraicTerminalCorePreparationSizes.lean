import Blotto.PlayerSpecificAlgebraicTerminalCoreDrawBounds

/-! Actual cached totals and the computed fractional quotient satisfy the
core size interface. The bound comes from the reached resource rows and
original lengths, with one fixed arithmetic layer. -/
namespace Blotto.PlayerSpecificAlgebraicTerminalCorePreparationSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicHeightEnvelope
open PlayerSpecificAlgebraicTerminalPreparation PlayerSpecificAlgebraicTerminalCoreFits
set_option autoImplicit false
set_option maxHeartbeats 2500000

def height (N H : ℕ) : ℕ := step (((H+1)*(N+N)+3)+H+1)

theorem fits {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0 < B) (hL : ∀ k,0 < lengths p x k ∧ lengths p x k ≤ B)
    (hb : InBox (lengths p x) (eval s x)) (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length ≤ 1)
    (H : ℕ) (hroot : HasHeight p.parameters.root.polynomial H) (hml : p.parameters.root.polynomial.length ≤ 4)
    (hBH : RationalHeight B H) (hsize : ∀ k,HasHeight (p.rows.read k).length H)
    (hresource : ∀ k,HasHeight (s.data.read k) H) :
    Fits p.parameters.root (PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B (prepare model p s B)) (height N H) := by
  let g := prepare model p s B
  let G := ((H+1)*(N+N)+3)+H+1
  have hHG : H ≤ G := by dsimp [G]; omega
  have hGG : (H+1)*(N+N)+3 ≤ G := by dsimp [G]; omega
  have hG1 : 1 ≤ G := by dsimp [G]; omega
  have hle : G ≤ step G := (Nat.le_succ _).trans (large G)
  have hm0 : p.parameters.root.polynomial ≠ [] := by intro hz; exact hc.irreducible.ne_zero (by rw [hz]; rfl)
  have hrootG := PlayerSpecificPolynomialHeights.mono hroot hHG
  have hcached := PlayerSpecificAlgebraicTerminalGroupBounds.cached_bounds model p s B x hc hs hB hL hb hmass hend H hsize
  refine ⟨?_,?_,?_⟩
  · exact ⟨PlayerSpecificAlgebraicField.constant_reduced _ B hc.normalized hm0,
      constant_height _ B G hrootG (hBH.mono hHG) hG1 hml⟩
  · intro j
    simp only [PlayerSpecificAlgebraicTerminalCoreInput.prepare,FixedArrayTable.read_ofFn]
    change Reduced p.parameters.root.polynomial (((g.groups[j.val]?).map (fun h => h.total)).getD []) ∧
      HasHeight (((g.groups[j.val]?).map (fun h => h.total)).getD []) (step G)
    by_cases hj : j.val < g.groups.length
    · rw [List.getElem?_eq_getElem hj,Option.map_some,Option.getD_some]
      have hg := hcached (g.groups[j.val]) (List.getElem_mem hj)
      exact ⟨hg.2.2.1,PlayerSpecificPolynomialHeights.mono hg.2.2.2.2.2 (hGG.trans hle)⟩
    · rw [List.getElem?_eq_none (by omega),Option.map_none,Option.getD_none]
      exact ⟨nil_reduced _ hm0,nil_height _⟩
  · intro ell probability hf
    change (g.fractional.map _)=some (ell,probability) at hf
    obtain ⟨k,hk,hpair⟩ := Option.map_eq_some_iff.mp hf
    have he : (p.rows.read k).length=ell := congrArg Prod.fst hpair
    have hq : PlayerSpecificAlgebraicField.divide p.parameters.root.polynomial (s.data.read k) (p.rows.read k).length=probability := congrArg Prod.snd hpair
    rw [← he,← hq]
    exact ⟨⟨hc.lengths k,PlayerSpecificPolynomialHeights.mono (hsize k) (hHG.trans hle)⟩,
      ⟨PlayerSpecificAlgebraicField.divide_reduced _ _ _ hc.normalized hm0,
        divide_height _ _ _ G hc.normalized hm0 hml (hs.reduced k) (hc.lengths k) hrootG
          (PlayerSpecificPolynomialHeights.mono (hresource k) hHG)
          (PlayerSpecificPolynomialHeights.mono (hsize k) hHG) hG1⟩⟩

end Blotto.PlayerSpecificAlgebraicTerminalCorePreparationSizes
