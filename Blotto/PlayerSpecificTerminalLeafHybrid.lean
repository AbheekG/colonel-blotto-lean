import Blotto.PlayerSpecificTerminalCoreHybrid

/-! The actual direct original-leaf output map preserves one fixed
exact-choice midpoint hybrid for every H, with no coordinate independence. -/
namespace Blotto.PlayerSpecificTerminalLeafHybrid
open MeasureTheory PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicHeightEnvelope
open PlayerSpecificAlgebraicTerminalPreparation
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem exists_hybrid {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0 < B) (hL : ∀ k,0 < lengths p x k ∧ lengths p x k ≤ B)
    (hb : InBox (lengths p x) (eval s x)) (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length ≤ 1)
    (T : ℕ) (hroot : HasHeight p.parameters.root.polynomial T) (hml : p.parameters.root.polynomial.length ≤ 4)
    (hBH : RationalHeight B T) (hsize : ∀ k,HasHeight (p.rows.read k).length T)
    (hresource : ∀ k,HasHeight (s.data.read k) T) (K : ℕ) :
    ∃ hybrid : Mixed N,∀ H,PlayerSpecificEventDistance.Bound
      (PlayerSpecificTerminalLeafLawGeometry.law p s B H K x) hybrid (80/(2:ℝ)^H) := by
  let model := RationalCostModel.schoolbook
  let g := prepare model p s B
  let a := PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B g
  let U := PlayerSpecificAlgebraicTerminalCorePreparationSizes.height N T
  have ha := PlayerSpecificAlgebraicTerminalCorePreparation.valid model p s B x hc hs hB hL hb hmass hend T hsize
  have hf := PlayerSpecificAlgebraicTerminalCorePreparationSizes.fits model p s B x hc hs hB hL hb hmass hend T hroot hml hBH hsize hresource
  have hTU : T ≤ U := by
    have h0 : T ≤ ((T+1)*(N+N)+3)+T+1 := by omega
    exact h0.trans ((Nat.le_succ _).trans (large _))
  have hU : 2 ≤ U := by
    have h0 : 2 ≤ ((T+1)*(N+N)+3)+T+1 := by omega
    exact h0.trans ((Nat.le_succ _).trans (large _))
  obtain ⟨G,_,_,_,_,hlaw⟩ := PlayerSpecificUniformLeafLawGeometry.geometry p s B x hc hs hB hL hb hmass hend T hsize K
  obtain ⟨hybrid,hevent⟩ := PlayerSpecificTerminalCoreHybrid.exists_hybrid p.parameters a hc.normalized hc.irreducible hc.interval x hc.root
    ha U hf hml (PlayerSpecificPolynomialHeights.mono hroot hTU) hU K
  refine ⟨hybrid.map (PlayerSpecificAlgebraicLeafValues.point G g.fractional),?_⟩
  intro H
  rw [hlaw H]
  exact PlayerSpecificEventDistance.map _ _ _ (hevent H) (PlayerSpecificAlgebraicLeafValues.point G g.fractional)
    (PlayerSpecificLeafMapLaw.measurable_point G g.fractional)

end Blotto.PlayerSpecificTerminalLeafHybrid
