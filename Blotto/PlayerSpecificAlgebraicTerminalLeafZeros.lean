import Blotto.PlayerSpecificAlgebraicFiniteDrawHeights

/-! A zero reached resource is emitted as a literal zero polynomial.
Neither direct splitting nor the optional fractional write changes it. -/
namespace Blotto.PlayerSpecificAlgebraicTerminalLeafZeros
open PlayerSpecificDensePolynomial PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicTerminalPreparation PlayerSpecificAlgebraicLeafAssignments
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem zero_resource {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hend : s.active.length ≤ 1) (hL : ∀ j,0 < lengths p x j)
    (j : Fin N) (hz : eval s x j=0) (H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) :
    (PlayerSpecificAlgebraicTerminalLeafExecution.run p s B H K bits).read j=[] := by
  let g := prepare RationalCostModel.schoolbook p s B
  let a := PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B g
  let y := PlayerSpecificAlgebraicTerminalCoreDraw.draw p.parameters a H K bits
  let L := fun k => (p.rows.read k).length
  have hj : ∀ h : Fin g.groups.length,j ∉ (g.groups.get h).members := by
    intro h hm
    have he := PlayerSpecificAlgebraicTerminalLeafGroups.member_saturated RationalCostModel.schoolbook p s B x hc h j hm
    rw [hz] at he
    exact ne_of_gt (hL j) he.symm
  change (emitMixed p.parameters.root L g.groups g.fractional y).read j=[]
  cases hf : g.fractional with
  | none => exact emit_inactive p.parameters.root L g.groups y j hj
  | some k =>
    have hne : j ≠ k := by
      intro he
      subst k
      have hfr := (fractional_value RationalCostModel.schoolbook p s B x hs hend j).mp hf
      exact ne_of_gt hfr.1 hz
    rw [emitMixed_other p.parameters.root L g.groups y k j hne]
    exact emit_inactive p.parameters.root L g.groups y j hj

end Blotto.PlayerSpecificAlgebraicTerminalLeafZeros
