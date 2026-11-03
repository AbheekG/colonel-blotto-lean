import Blotto.PlayerSpecificAlgebraicTerminalLeafGroups

/-! One actual grouping and one computed four-slot core feed the native
original-leaf allocator. Every bit string gives a nonnegative allocation
spending the player budget exactly before downward rational rounding. -/
namespace Blotto.PlayerSpecificAlgebraicTerminalLeafExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicTerminalPreparation PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (B : ℚ)
    (H K : ℕ) (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) : FixedArrayTable N Data :=
  let g := prepare RationalCostModel.schoolbook p s B
  let a := PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B g
  let y := PlayerSpecificAlgebraicTerminalCoreDraw.draw p.parameters a H K bits
  PlayerSpecificAlgebraicLeafAssignments.emitMixed p.parameters.root (fun j => (p.rows.read j).length) g.groups g.fractional y

theorem every_path {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (B : ℚ) (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x s) (hB : 0 < B) (hL : ∀ k,0 < lengths p x k ∧ lengths p x k ≤ B)
    (hb : InBox (lengths p x) (eval s x)) (hmass : (∑ k,eval s x k)=2*(B:ℝ)) (hend : s.active.length ≤ 1)
    (T : ℕ) (hroot : HasHeight p.parameters.root.polynomial T) (hml : p.parameters.root.polynomial.length ≤ 4)
    (hBH : RationalHeight B T) (hsize : ∀ k,HasHeight (p.rows.read k).length T)
    (hresource : ∀ k,HasHeight (s.data.read k) T) (H K : ℕ)
    (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) :
    FullBudget (B:ℝ) (values (run p s B H K bits) x) := by
  let g := prepare RationalCostModel.schoolbook p s B
  let a := PlayerSpecificAlgebraicTerminalCoreInput.prepare p s B g
  let y := PlayerSpecificAlgebraicTerminalCoreDraw.draw p.parameters a H K bits
  let L := fun j => (p.rows.read j).length
  have hm0 : p.parameters.root.polynomial ≠ [] := by intro hz; exact hc.irreducible.ne_zero (by rw [hz]; rfl)
  have hn := PlayerSpecificAlgebraicTerminalGroupBounds.members_nodup RationalCostModel.schoolbook p s B x hc
  have hcache := groups_cached RationalCostModel.schoolbook p s B hc.normalized hm0 hc.lengths
  have hcached := PlayerSpecificAlgebraicTerminalGroupBounds.cached_bounds RationalCostModel.schoolbook p s B x hc hs hB hL hb hmass hend T hsize
  have hpos : ∀ h ∈ g.groups,0 < realEvaluate h.total x := fun h hh => (hcached h hh).2.2.2.1
  let G := PlayerSpecificAlgebraicLeafPartition.partition p.parameters.root L g.groups x (fun j => (hL j).1) hn hcache hpos
  have hy : FullBudget (B:ℝ) (values y x) :=
    (PlayerSpecificAlgebraicTerminalCoreExecution.every_path p s B x hc hs hB hL hb hmass hend T hroot hml hBH hsize hresource H K bits).1
  have hcount0 := groups_count RationalCostModel.schoolbook p s B x hc hs hB hL hb hmass hend
  have hcount : g.groups.length=2 ∨ g.groups.length=3 := by
    change 2 ≤ g.groups.length ∧ g.groups.length ≤ 3 at hcount0
    omega
  have hz : g.groups.length=2 → values y x 2=0 := by
    intro htwo
    have he := PlayerSpecificAlgebraicTerminalCoreDraw.two_unused p.parameters a H K bits htwo
    change realEvaluate (y.read 2) x=0
    rw [he]
    rfl
  have hnone : g.fractional=none → values y x 3=0 := by
    intro hn0
    have hf : a.fractional=none := by
      change (g.fractional.map _)=none
      rw [hn0]
      rfl
    have he := PlayerSpecificAlgebraicTerminalCoreDraw.no_fraction_last p.parameters a H K bits hf
    change realEvaluate (y.read 3) x=0
    rw [he]
    rfl
  have hp : ∀ k,g.fractional=some k → ∀ h : Fin g.groups.length,k ∉ (g.groups.get h).members :=
    fun k hk h => PlayerSpecificAlgebraicTerminalLeafGroups.fractional_not_member RationalCostModel.schoolbook p s B x hc hs hend k hk h
  have he := PlayerSpecificAlgebraicLeafValues.mixed_value p.parameters.root L g.groups x (fun j => (hL j).1) hn hcache hpos
    hc.normalized hc.irreducible hc.root.1 g.fractional hp y
  change FullBudget (B:ℝ) (values (PlayerSpecificAlgebraicLeafAssignments.emitMixed p.parameters.root L g.groups g.fractional y) x)
  rw [he]
  exact PlayerSpecificAlgebraicLeafBudget.point_fullBudget G g.fractional (values y x) B hy hcount hz hnone

end Blotto.PlayerSpecificAlgebraicTerminalLeafExecution
