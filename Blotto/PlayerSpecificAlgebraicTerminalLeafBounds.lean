import Blotto.PlayerSpecificAlgebraicLeafHeights

/-! Every reached terminal leaf has a bound derived from actual group
totals, actual core output and original endpoint rows. -/
namespace Blotto.PlayerSpecificAlgebraicTerminalLeafBounds
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicTerminalPreparation PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def base (N T K : ℕ) : ℕ := PlayerSpecificAlgebraicTerminalCoreExecution.height N T K+((T+1)*(N+N)+3)+T+1
def height (N T K : ℕ) : ℕ := iterate 2 (base N T K)

theorem bounds {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0 < B) (hL : ∀ k,0 < lengths p x k ∧ lengths p x k ≤ B)
    (hb : InBox (lengths p x) (eval s x)) (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length ≤ 1)
    (T : ℕ) (hroot : HasHeight p.parameters.root.polynomial T) (hml : p.parameters.root.polynomial.length ≤ 4)
    (hBH : RationalHeight B T) (hsize : ∀ k,HasHeight (p.rows.read k).length T)
    (hresource : ∀ k,HasHeight (s.data.read k) T) (H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) :
    ∀ j,PlayerSpecificAlgebraicReduction.Reduced p.parameters.root.polynomial
        ((PlayerSpecificAlgebraicTerminalLeafExecution.run p s B H K bits).read j) ∧
      HasHeight ((PlayerSpecificAlgebraicTerminalLeafExecution.run p s B H K bits).read j) (height N T K) := by
  let g := prepare RationalCostModel.schoolbook p s B
  let a := PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B g
  let y := PlayerSpecificAlgebraicTerminalCoreDraw.draw p.parameters a H K bits
  let S := base N T K
  have hTS : T ≤ S := by dsimp [S,base]; omega
  have hGS : (T+1)*(N+N)+3 ≤ S := by dsimp [S,base]; omega
  have hYS : PlayerSpecificAlgebraicTerminalCoreExecution.height N T K ≤ S := by dsimp [S,base]; omega
  have hS : 1 ≤ S := by dsimp [S,base]; omega
  have hm0 : p.parameters.root.polynomial ≠ [] := by intro hz; exact hc.irreducible.ne_zero (by rw [hz]; rfl)
  have hy : ∀ j,PlayerSpecificAlgebraicReduction.Reduced p.parameters.root.polynomial (y.read j) ∧
      HasHeight (y.read j) S := by
    have hy0 := (PlayerSpecificAlgebraicTerminalCoreExecution.every_path p s B x hc hs hB hL hb hmass hend
      T hroot hml hBH hsize hresource H K bits).2
    intro j
    exact ⟨(hy0 j).1,PlayerSpecificPolynomialHeights.mono (hy0 j).2 hYS⟩
  have hg := PlayerSpecificAlgebraicTerminalGroupBounds.cached_bounds RationalCostModel.schoolbook p s B x hc hs hB hL hb hmass hend T hsize
  exact PlayerSpecificAlgebraicLeafHeights.mixed_bounds p.parameters.root (fun j => (p.rows.read j).length) g.groups g.fractional y S
    hc.normalized hm0 hml (PlayerSpecificPolynomialHeights.mono hroot hTS) hS
    (fun j => ⟨hc.lengths j,PlayerSpecificPolynomialHeights.mono (hsize j) hTS⟩)
    (fun h hh => ⟨(hg h hh).2.2.1,PlayerSpecificPolynomialHeights.mono (hg h hh).2.2.2.2.2 hGS⟩) hy

end Blotto.PlayerSpecificAlgebraicTerminalLeafBounds
