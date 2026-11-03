import Blotto.PlayerSpecificTerminalLeafHybrid

/-! The complete actual field sampler has one fixed exact-choice
finite-midpoint hybrid. Reached-state certificates select only proof-law
witnesses; the executing sampler retains its original single path. -/
namespace Blotto.PlayerSpecificFiniteFieldHybrid
open MeasureTheory PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem prepared {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (B : ℚ) (player : Bool)
    (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x)
    (hs : Valid p x (start RationalCostModel.schoolbook p player))
    (hB : 0 < (if player then 1 else B : ℚ))
    (hL : ∀ j,0 < lengths p x j ∧ lengths p x j ≤ ((if player then 1 else B : ℚ):ℝ))
    (T : ℕ) (hroot : HasHeight p.parameters.root.polynomial T) (hml : p.parameters.root.polynomial.length ≤ 4)
    (hBH : RationalHeight (if player then 1 else B : ℚ) T) (hsize : ∀ j,HasHeight (p.rows.read j).length T)
    (hleaves : PlayerSpecificResourceIdealLeaves.ForLeaves RationalCostModel.schoolbook p
      (fun s => Valid p x s ∧ InBox (lengths p x) (eval s x) ∧
        (∑ j,eval s x j)=2*(((if player then 1 else B : ℚ):ℝ)) ∧ s.active.length ≤ 1 ∧
          ∀ j,HasHeight (s.data.read j) T) (N-1) (start RationalCostModel.schoolbook p player)) (K : ℕ) :
    ∃ hybrid : Mixed N,∀ H,PlayerSpecificEventDistance.Bound (PlayerSpecificFiniteFieldCDF.law p B player H K x)
      hybrid (((N-1+80:ℕ):ℝ)/(2:ℝ)^H) := by
  classical
  let b : ℚ := if player then 1 else B
  let P := fun s : State N => Valid p x s ∧ InBox (lengths p x) (eval s x) ∧
    (∑ j,eval s x j)=2*(b:ℝ) ∧ s.active.length ≤ 1 ∧ ∀ j,HasHeight (s.data.read j) T
  have hex : ∀ s,P s → ∃ hybrid : Mixed N,∀ H,PlayerSpecificEventDistance.Bound
      (PlayerSpecificTerminalLeafLawGeometry.law p s b H K x) hybrid (80/(2:ℝ)^H) := by
    intro s hstate
    exact PlayerSpecificTerminalLeafHybrid.exists_hybrid p s b x hc hstate.1 hB hL hstate.2.1 hstate.2.2.1 hstate.2.2.2.1
      T hroot hml hBH hsize hstate.2.2.2.2 K
  let leaf := fun s : State N => if h : P s then Classical.choose (hex s h) else segmentLaw 0 0
  let draw := fun (H : ℕ) (s : State N) (bits : Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool) =>
    PlayerSpecificAlgebraicSegment.values (PlayerSpecificAlgebraicTerminalLeafExecution.run p s b H K bits) x
  have hleaf : ∀ H,PlayerSpecificResourceIdealLeaves.ForLeaves RationalCostModel.schoolbook p
      (fun s => PlayerSpecificEventDistance.Bound
        ((fairBitLaw (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K)).map (draw H s)) (leaf s) (80/(2:ℝ)^H))
        (N-1) (start RationalCostModel.schoolbook p player) := by
    intro H
    apply PlayerSpecificResourceIdealLeaves.mono RationalCostModel.schoolbook p _ _ (N-1)
      (start RationalCostModel.schoolbook p player) hleaves
    intro s hstate
    change PlayerSpecificEventDistance.Bound (PlayerSpecificTerminalLeafLawGeometry.law p s b H K x)
      (if h : P s then Classical.choose (hex s h) else segmentLaw 0 0) (80/(2:ℝ)^H)
    rw [dite_eq_left hstate]
    exact Classical.choose_spec (hex s hstate) H
  refine ⟨PlayerSpecificResourceIdealLaw.law RationalCostModel.schoolbook p x leaf (N-1)
    (start RationalCostModel.schoolbook p player)
      (PlayerSpecificResourceIdealMean.of_valid RationalCostModel.schoolbook p x hc (N-1)
        (start RationalCostModel.schoolbook p player) hs),?_⟩
  exact PlayerSpecificResourceHybrid.event_bound RationalCostModel.schoolbook p x hc (N-1)
    (start RationalCostModel.schoolbook p player) hs (fun H => PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) draw leaf 80 hleaf

end Blotto.PlayerSpecificFiniteFieldHybrid
