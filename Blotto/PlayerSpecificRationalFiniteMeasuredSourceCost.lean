import Blotto.PlayerSpecificRationalOutputSourceCost
import Blotto.PlayerSpecificAlgebraicFiniteDrawHeights

/-! The same accepted finite packet pays for its complete algebraic draw,
all original-coordinate dyadic floors, and the final control. -/
namespace Blotto.PlayerSpecificRationalFiniteMeasuredSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def algebraicHeight {N : ℕ} (i : RationalPlayerSpecificInput N) (K : ℕ) : ℕ :=
  PlayerSpecificAlgebraicFiniteDrawHeights.coefficient*(N+1)^3*
    (PlayerSpecificInitialPositivePrecision.inputSize i+K+1)

def combinedHeight {N : ℕ} (i : RationalPlayerSpecificInput N) (K : ℕ) : ℕ :=
  max (algebraicHeight i K)
    (PlayerSpecificResourceEntryInput.height N (PlayerSpecificInitialPositivePrecision.inputSize i))

def work {N : ℕ} (i : RationalPlayerSpecificInput N) (H K P : ℕ) : ℕ :=
  PlayerSpecificFiniteDrawMeasuredSourceCost.work i H K+
  PlayerSpecificRationalOutputSourceCost.work N (combinedHeight i K) P+
  3*RationalCostModel.schoolbook.rat
    (PlayerSpecificRationalOutputSourceCost.width N (combinedHeight i K) P)

theorem original_input {N : ℕ} (i : RationalPlayerSpecificInput N)
    (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
    ∀ (player : Bool) (H K P : ℕ)
      (bits : Fin (PlayerSpecificAlgebraicFiniteDraw.bitCount N H K) → Bool),
      (PlayerSpecificRationalFiniteMeasuredExecution.run p i.budget player H K P bits).1=
        PlayerSpecificRationalFiniteDraw.draw p i.budget player H K P bits ∧
      (PlayerSpecificRationalFiniteMeasuredExecution.run p i.budget player H K P bits).2≤
        work i H K P := by
  dsimp only
  let p:=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r
  let T:=combinedHeight i
  obtain ⟨x,hx,hdraw⟩:=PlayerSpecificAlgebraicFiniteDrawHeights.original_input i r hr
  intro player H K P bits
  let drawn:=PlayerSpecificFiniteDrawMeasuredExecution.run p i.budget player H K bits
  let rounded:=PlayerSpecificRationalOutputExecution.run p.parameters.root drawn.1 P
  have hfinite:=PlayerSpecificFiniteDrawMeasuredSourceCost.original_input i r hr player H K bits
  have hrows : ∀ j : Fin N,PlayerSpecificAlgebraicReduction.Reduced p.parameters.root.polynomial
      (drawn.1.read j) ∧ HasHeight (drawn.1.read j) (T K) := by
    intro j
    rw [show drawn.1=PlayerSpecificAlgebraicFiniteDraw.draw p i.budget player H K bits from hfinite.1]
    exact ⟨((hdraw player H K bits).2 j).1,
      PlayerSpecificPolynomialHeights.mono (((hdraw player H K bits).2 j).2)
        (le_max_left _ _)⟩
  have hroot:=PlayerSpecificResourceEntryInput.original_input i r hr
  obtain ⟨_,_,hc,hml,hrh,heh,_,_,_⟩:=hroot
  have hroot0 : p.parameters.root.polynomial≠[] := by
    intro hz
    exact hc.irreducible.ne_zero (by rw [hz]; rfl)
  have hround:=PlayerSpecificRationalOutputSourceCost.cost p.parameters.root drawn.1
    (T K) P hc.normalized hroot0 hml
    hc.interval
    (PlayerSpecificPolynomialHeights.mono hrh (le_max_right _ _))
    (PlayerSpecificPolynomialHeights.mono heh (le_max_right _ _)) hrows
  have hW : 1≤PlayerSpecificRationalOutputSourceCost.width N (T K) P := by
    unfold PlayerSpecificRationalOutputSourceCost.width
    have h:=(PlayerSpecificAlgebraicActiveListCost.width_large
      (PlayerSpecificRationalOutputSourceCost.frameHeight N (T K) P)).1
    omega
  have hPW : binaryWordWidth P≤PlayerSpecificRationalOutputSourceCost.width N (T K) P := by
    have hbase : P≤PlayerSpecificRationalOutputSourceCost.frameHeight N (T K) P := by
      dsimp [PlayerSpecificRationalOutputSourceCost.frameHeight,
        PlayerSpecificOutputFloorPredicateSourceCost.height,
        PlayerSpecificOutputFloorPredicateSourceCost.inputHeight]
      have hl:=PlayerSpecificAlgebraicHeightEnvelope.large
        (max (T K) (P+2)+2)
      omega
    exact (control_width P).trans ((Nat.add_le_add_right hbase 1).trans
      (PlayerSpecificAlgebraicActiveListCost.width_large _).2.2)
  have hcontrol:=PlayerSpecificAlgebraicCallerFrame.controls_cost
    RationalCostModel.schoolbook [P]
    (PlayerSpecificRationalOutputSourceCost.width N (T K) P)
    (by intro word hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw;
        rw [hw]; exact hPW) hW
  have hcontrol' : price RationalCostModel.schoolbook [.control P]≤
      3*RationalCostModel.schoolbook.rat
        (PlayerSpecificRationalOutputSourceCost.width N (T K) P) := by
    simpa only [List.map_cons,List.map_nil,List.length_cons,List.length_nil,
      Nat.reduceAdd,Nat.reduceMul] using hcontrol
  refine ⟨PlayerSpecificRationalFiniteMeasuredExecution.value p i.budget player H K P bits,?_⟩
  change drawn.2+rounded.2+price RationalCostModel.schoolbook [.control P]≤_
  change drawn.2+rounded.2+price RationalCostModel.schoolbook [.control P]≤
    PlayerSpecificFiniteDrawMeasuredSourceCost.work i H K+
      PlayerSpecificRationalOutputSourceCost.work N (T K) P+
      3*RationalCostModel.schoolbook.rat
        (PlayerSpecificRationalOutputSourceCost.width N (T K) P)
  exact Nat.add_le_add (Nat.add_le_add hfinite.2 hround) hcontrol'

end Blotto.PlayerSpecificRationalFiniteMeasuredSourceCost
