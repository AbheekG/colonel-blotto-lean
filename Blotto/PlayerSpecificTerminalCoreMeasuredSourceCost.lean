import Blotto.PlayerSpecificTerminalCoreMeasuredExecution

/-! Complete reached-state source work for the actual terminal core:
grouping and quotient feed the four-case draw without a supplied core. -/
namespace Blotto.PlayerSpecificTerminalCoreMeasuredSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (N T H K : ℕ) : ℕ :=
  PlayerSpecificTerminalCoreInputSourceCost.work N T+
  PlayerSpecificTerminalCoreDrawSourceCost.work
    (PlayerSpecificAlgebraicTerminalCorePreparationSizes.height N T) H K+2

theorem cost {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ)
    (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0 < B)
    (hL : ∀ k,0 < lengths p x k ∧ lengths p x k ≤ B)
    (hb : InBox (lengths p x) (eval s x))
    (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length ≤ 1)
    (T : ℕ) (hroot : HasHeight p.parameters.root.polynomial T)
    (hml : p.parameters.root.polynomial.length ≤ 4)
    (heB : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi,B] T)
    (hBH : RationalHeight B T)
    (hsize : ∀ k,HasHeight (p.rows.read k).length T)
    (hresource : ∀ k,HasHeight (s.data.read k) T) (hT : 2 ≤ T)
    (H K : ℕ) (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) :
    (PlayerSpecificTerminalCoreMeasuredExecution.run p s B H K bits).2 ≤ work N T H K := by
  let model := RationalCostModel.schoolbook
  let U := PlayerSpecificAlgebraicTerminalCorePreparationSizes.height N T
  let input := PlayerSpecificTerminalCoreInputExecution.run p s B
  let drawn := PlayerSpecificTerminalCoreDrawExecution.run p.parameters input.1 H K bits
  have hinput := PlayerSpecificTerminalCoreInputSourceCost.cost p s B x hc hs hB hL hb hmass hend
    T hroot hml heB hBH hsize hresource hT
  have hvalid : PlayerSpecificAlgebraicTerminalCoreInput.Valid input.1 x := by
    dsimp only [input]
    rw [PlayerSpecificTerminalCoreInputExecution.value]
    exact PlayerSpecificAlgebraicTerminalCorePreparation.valid model p s B x hc hs hB hL hb hmass hend T hsize
  have hfit : PlayerSpecificAlgebraicTerminalCoreFits.Fits p.parameters.root input.1 U := by
    dsimp only [input]
    rw [PlayerSpecificTerminalCoreInputExecution.value]
    exact PlayerSpecificAlgebraicTerminalCorePreparationSizes.fits model p s B x hc hs hB hL hb hmass hend
      T hroot hml hBH hsize hresource
  have hTU : T ≤ U := by
    have h0 : T ≤ ((T+1)*(N+N)+3)+T+1 := by omega
    exact h0.trans ((Nat.le_succ _).trans
      (PlayerSpecificAlgebraicHeightEnvelope.large _))
  have hends : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] T := by
    intro q hq
    apply heB
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    tauto
  have hdraw := PlayerSpecificTerminalCoreDrawSourceCost.cost p.parameters input.1 x U H K bits
    hc.normalized hc.irreducible hc.interval hc.root hvalid hfit hml
    (mono hroot hTU) (mono hends hTU) (hT.trans hTU)
  change input.2+drawn.2+price model [.control 1] ≤ _
  rw [show price model [.control 1]=2 by rfl]
  exact Nat.add_le_add_right (Nat.add_le_add hinput hdraw) 2

theorem same_return_and_cost {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ)
    (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0 < B)
    (hL : ∀ k,0 < lengths p x k ∧ lengths p x k ≤ B)
    (hb : InBox (lengths p x) (eval s x))
    (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length ≤ 1)
    (T : ℕ) (hroot : HasHeight p.parameters.root.polynomial T)
    (hml : p.parameters.root.polynomial.length ≤ 4)
    (heB : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi,B] T)
    (hBH : RationalHeight B T)
    (hsize : ∀ k,HasHeight (p.rows.read k).length T)
    (hresource : ∀ k,HasHeight (s.data.read k) T) (hT : 2 ≤ T)
    (H K : ℕ) (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) :
    (PlayerSpecificTerminalCoreMeasuredExecution.run p s B H K bits).1 =
      PlayerSpecificAlgebraicTerminalCoreExecution.run p s B H K bits ∧
    (PlayerSpecificTerminalCoreMeasuredExecution.run p s B H K bits).2 ≤ work N T H K :=
  ⟨PlayerSpecificTerminalCoreMeasuredExecution.value p s B H K bits,
    cost p s B x hc hs hB hL hb hmass hend T hroot hml heB hBH hsize hresource hT H K bits⟩

end Blotto.PlayerSpecificTerminalCoreMeasuredSourceCost
