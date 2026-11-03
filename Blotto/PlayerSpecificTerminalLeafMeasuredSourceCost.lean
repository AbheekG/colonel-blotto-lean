import Blotto.PlayerSpecificTerminalLeafMeasuredExecution

/-! Complete source price and exact native return for one reached terminal
leaf. The same cached grouping feeds the core and original-coordinate rows. -/
namespace Blotto.PlayerSpecificTerminalLeafMeasuredSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (N T H K : ℕ) : ℕ :=
  PlayerSpecificTerminalCoreMeasuredSourceCost.work N T H K+
  PlayerSpecificTerminalLeafEmissionSourceCost.work N T K+2

theorem cost {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ)
    (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0<B)
    (hL : ∀ k,0<lengths p x k ∧ lengths p x k≤B)
    (hb : InBox (lengths p x) (eval s x))
    (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length≤1)
    (T : ℕ) (hroot : HasHeight p.parameters.root.polynomial T)
    (hml : p.parameters.root.polynomial.length≤4)
    (heB : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi,B] T)
    (hBH : RationalHeight B T)
    (hsize : ∀ k,HasHeight (p.rows.read k).length T)
    (hresource : ∀ k,HasHeight (s.data.read k) T) (hT : 2≤T)
    (H K : ℕ) (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) :
    (PlayerSpecificTerminalLeafMeasuredExecution.run p s B H K bits).2≤work N T H K := by
  let model:=RationalCostModel.schoolbook
  let grouped:=PlayerSpecificTerminalPreparationExecution.run model p s B
  let input:=PlayerSpecificTerminalCoreInputExecution.fromPrepared p s B grouped.1
  let drawn:=PlayerSpecificTerminalCoreDrawExecution.run p.parameters input.1 H K bits
  let emitted:=PlayerSpecificTerminalLeafEmissionExecution.fromCore model p.parameters.root
    (fun j => (p.rows.read j).length) grouped.1.groups grouped.1.fractional drawn.1
  have hcore := PlayerSpecificTerminalCoreMeasuredSourceCost.cost p s B x hc hs hB hL hb hmass hend
    T hroot hml heB hBH hsize hresource hT H K bits
  have hcore' : grouped.2+input.2+2+drawn.2+2≤
      PlayerSpecificTerminalCoreMeasuredSourceCost.work N T H K := by
    change grouped.2+input.2+price model [.control 1]+drawn.2+
      price model [.control 1]≤_ at hcore
    simpa only [show price model [.control 1]=2 by rfl] using hcore
  have he : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] T := by
    intro q hq
    apply heB
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    tauto
  have hleaf := PlayerSpecificTerminalLeafEmissionSourceCost.cost p s B x hc hs hB hL hb hmass hend
    T hroot hml he hBH hsize hresource H K bits
  have hleaf' : emitted.2≤PlayerSpecificTerminalLeafEmissionSourceCost.work N T K := by
    dsimp only [emitted]
    rw [PlayerSpecificTerminalCoreDrawExecution.value,
      PlayerSpecificTerminalCoreInputExecution.fromPrepared_value,
      PlayerSpecificTerminalPreparationExecution.value]
    exact hleaf
  change grouped.2+input.2+drawn.2+emitted.2+
    price model [.control 1]≤_
  have hcontrol : price model [.control 1]=2 := by rfl
  rw [hcontrol]
  dsimp only [work]
  omega

theorem full_budget {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ)
    (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0<B)
    (hL : ∀ k,0<lengths p x k ∧ lengths p x k≤B)
    (hb : InBox (lengths p x) (eval s x))
    (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length≤1)
    (T : ℕ) (hroot : HasHeight p.parameters.root.polynomial T)
    (hml : p.parameters.root.polynomial.length≤4)
    (hBH : RationalHeight B T)
    (hsize : ∀ k,HasHeight (p.rows.read k).length T)
    (hresource : ∀ k,HasHeight (s.data.read k) T)
    (H K : ℕ) (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) :
    FullBudget (B:ℝ) (values
      (PlayerSpecificTerminalLeafMeasuredExecution.run p s B H K bits).1 x) := by
  rw [PlayerSpecificTerminalLeafMeasuredExecution.value]
  exact PlayerSpecificAlgebraicTerminalLeafExecution.every_path p s B x hc hs hB hL hb hmass hend
    T hroot hml hBH hsize hresource H K bits

theorem same_return_and_cost {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ)
    (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0<B)
    (hL : ∀ k,0<lengths p x k ∧ lengths p x k≤B)
    (hb : InBox (lengths p x) (eval s x))
    (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length≤1)
    (T : ℕ) (hroot : HasHeight p.parameters.root.polynomial T)
    (hml : p.parameters.root.polynomial.length≤4)
    (heB : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi,B] T)
    (hBH : RationalHeight B T)
    (hsize : ∀ k,HasHeight (p.rows.read k).length T)
    (hresource : ∀ k,HasHeight (s.data.read k) T) (hT : 2≤T)
    (H K : ℕ) (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) :
    (PlayerSpecificTerminalLeafMeasuredExecution.run p s B H K bits).1 =
      PlayerSpecificAlgebraicTerminalLeafExecution.run p s B H K bits ∧
    (PlayerSpecificTerminalLeafMeasuredExecution.run p s B H K bits).2≤work N T H K :=
  ⟨PlayerSpecificTerminalLeafMeasuredExecution.value p s B H K bits,
    cost p s B x hc hs hB hL hb hmass hend T hroot hml heB hBH hsize hresource hT H K bits⟩

end Blotto.PlayerSpecificTerminalLeafMeasuredSourceCost
