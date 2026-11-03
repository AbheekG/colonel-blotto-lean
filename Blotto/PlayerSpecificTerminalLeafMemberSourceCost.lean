import Blotto.PlayerSpecificTerminalLeafEmissionExecution

/-! One original-coordinate assignment pays for the executed field
division, product, and the two stored indices. The height of its quotient
comes from the cached group total, not from a supplied arithmetic oracle. -/
namespace Blotto.PlayerSpecificTerminalLeafMemberSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicGrouping PlayerSpecificAlgebraicLeafAssignments
set_option autoImplicit false
set_option maxHeartbeats 2500000

def height (N T K : ℕ) : ℕ :=
  step (PlayerSpecificAlgebraicTerminalLeafBounds.base N T K)+N+7

def work (model : RationalCostModel) (N T K : ℕ) : ℕ :=
  16000000009*model.rat (PlayerSpecificAlgebraicComparisonExecution.width (height N T K))

theorem cost {N : ℕ} (model : RationalCostModel) (root : Candidate)
    (length : Fin N → Data) (groups : List (Group N)) (y : FixedArrayTable 4 Data)
    (g : Fin groups.length) (j : Fin N) (T K : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T)
    (hL : ∀ j,Reduced root.polynomial (length j) ∧ HasHeight (length j) T)
    (hG : ∀ g∈groups,Reduced root.polynomial g.total ∧
      HasHeight g.total ((T+1)*(N+N)+3))
    (hy : ∀ j,Reduced root.polynomial (y.read j) ∧
      HasHeight (y.read j) (PlayerSpecificAlgebraicTerminalCoreExecution.height N T K))
    (hgcount : groups.length≤3) :
    (PlayerSpecificTerminalLeafEmissionExecution.member model root length groups y g j).2≤
      work model N T K := by
  let B := PlayerSpecificAlgebraicTerminalLeafBounds.base N T K
  let S := height N T K
  let W := PlayerSpecificAlgebraicComparisonExecution.width S
  let total := (groups.get g).total
  let a := length j
  let b := y.read (slot g)
  let quotient := PlayerSpecificAlgebraicExpressionExecution.binary model root .divide a total
  let product := PlayerSpecificAlgebraicExpressionExecution.binary model root .multiply quotient.1 b
  have hTB : T≤B := by dsimp [B,PlayerSpecificAlgebraicTerminalLeafBounds.base]; omega
  have hGB : (T+1)*(N+N)+3≤B := by dsimp [B,PlayerSpecificAlgebraicTerminalLeafBounds.base]; omega
  have hYB : PlayerSpecificAlgebraicTerminalCoreExecution.height N T K≤B := by
    dsimp [B,PlayerSpecificAlgebraicTerminalLeafBounds.base]; omega
  have hBS : B≤S := by
    change B≤step B+N+7
    have hb : B≤step B := (Nat.le_succ B).trans (large B)
    omega
  have hstep : step B≤S := by change step B≤step B+N+7; omega
  have hS : 1≤S := by dsimp [S,height]; omega
  have htotal := hG (groups.get g) (List.get_mem groups g)
  have hq : Reduced root.polynomial quotient.1 ∧ HasHeight quotient.1 (step B) := by
    rw [show quotient.1=PlayerSpecificAlgebraicField.divide root.polynomial a total by
      exact PlayerSpecificAlgebraicExpressionExecution.binary_value model root .divide a total]
    exact ⟨PlayerSpecificAlgebraicField.divide_reduced _ _ _ hm hm0,
      divide_height root.polynomial a total B hm hm0 hml
        (hL j).1 htotal.1 (mono hmT hTB) (mono (hL j).2 hTB)
        (mono htotal.2 hGB) (by omega)⟩
  have hd := PlayerSpecificAlgebraicExpressionPrimitiveCost.binary_cost model root .divide a total S
    hm hm0 hml (hL j).1 htotal.1 (mono hmT (hTB.trans hBS))
    (mono (hL j).2 (hTB.trans hBS)) (mono htotal.2 (hGB.trans hBS)) hS
  have hp := PlayerSpecificAlgebraicExpressionPrimitiveCost.binary_cost model root .multiply quotient.1 b S
    hm hm0 hml hq.1 (hy (slot g)).1 (mono hmT (hTB.trans hBS))
    (mono hq.2 hstep) (mono (hy (slot g)).2 (hYB.trans hBS)) hS
  have hwords : ∀ word∈[g.val,j.val,1],binaryWordWidth word≤W := by
    intro word hw
    have hsmall : word≤S := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with hw|hw|hw
      · rw [hw]; have hg := g.isLt; omega
      · rw [hw]; have hj := j.isLt; dsimp [S,height]; omega
      · rw [hw]; omega
    exact (control_width word).trans ((Nat.add_le_add_right hsmall 1).trans
      (PlayerSpecificAlgebraicActiveListCost.width_large S).2.2)
  have hc := PlayerSpecificAlgebraicCallerFrame.controls_cost model [g.val,j.val,1] W hwords
    (by have h := (PlayerSpecificAlgebraicActiveListCost.width_large S).1; omega)
  have hc' : price model [.control g.val,.control j.val,.control 1]≤9*model.rat W := by
    change price model ([g.val,j.val,1].map Event.control)≤9*model.rat W
    simpa only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceMul] using hc
  change quotient.2≤8000000000*model.rat W at hd
  change product.2≤8000000000*model.rat W at hp
  change quotient.2+product.2+price model [.control g.val,.control j.val,.control 1]≤
    16000000009*model.rat W
  omega

end Blotto.PlayerSpecificTerminalLeafMemberSourceCost
