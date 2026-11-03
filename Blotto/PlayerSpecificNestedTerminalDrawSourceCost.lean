import Blotto.PlayerSpecificNestedTerminalDrawExecution

/-! The complete original-row-height terminal nested draw source
bound includes resource conversion, all nested branches and restored
allocation arrays. Runtime supplies no size/arithmetic/cost oracle. -/
namespace Blotto.PlayerSpecificNestedTerminalDrawSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedTerminalInput PlayerSpecificAlgebraicNestedTerminalSizes PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def outputHeight (T K : ℕ) : ℕ := PlayerSpecificAlgebraicNestedInteriorDraw.height (step T) K
def work (T H K : ℕ) : ℕ := PlayerSpecificNestedTerminalPreparationSourceCost.work T+
  PlayerSpecificNestedSpecDrawSourceCost.work (step T) H K+PlayerSpecificNestedRestoreSourceCost.work (outputHeight T K)+2

theorem height_lower (T K : ℕ) : T≤outputHeight T K := by
  have h0 : T≤step T := (Nat.le_succ _).trans (large T)
  have h1:=PlayerSpecificAlgebraicNestedInteriorSizes.input_le (step T) K
  have h2:=PlayerSpecificAlgebraicExpressionBudget.initial_le 3 (PlayerSpecificAlgebraicNestedInteriorSizes.height (step T) K+2*K+6)
  change T ≤ iterate 3 (PlayerSpecificAlgebraicNestedInteriorSizes.height (step T) K+2*K+6)
  omega

theorem cost (root : Candidate) (a : Input) (T H K : ℕ) (bits : Fin ((17*H+K)+K) → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo<root.interval.hi) (hT : 2≤T) (ha : Fits root a T) :
    (PlayerSpecificNestedTerminalDrawExecution.run RationalCostModel.schoolbook root a H K bits).2≤work T H K := by
  let model:=RationalCostModel.schoolbook
  let p:=(PlayerSpecificNestedTerminalPreparationExecution.run model root a).1
  let U:=outputHeight T K
  have hbase : T≤step T := (Nat.le_succ _).trans (large T)
  have hTU : T≤U := height_lower T K
  have hp:=PlayerSpecificNestedTerminalPreparationSourceCost.input_bounds model root a T hm hm0 hml hmT (by omega) ha
  have hc:=PlayerSpecificNestedTerminalPreparationSourceCost.cost root a T hm hm0 hml hmT he hv (by omega) ha
  have hd:=PlayerSpecificNestedSpecDrawSourceCost.cost root p.input (step T) H K bits hm hm0 hml (mono hmT hbase) (mono he hbase) hv
    (hT.trans hbase) hp
  have hy : ∀ j,Reduced root.polynomial ((PlayerSpecificNestedSpecDrawExecution.run model root p.input H K bits).1.read j) ∧
      HasHeight ((PlayerSpecificNestedSpecDrawExecution.run model root p.input H K bits).1.read j) U := by
    intro j
    rw [PlayerSpecificNestedSpecDrawExecution.value]
    exact ⟨PlayerSpecificAlgebraicNestedSpecDraw.reduced model root p.input H K bits hm hm0 j,
      PlayerSpecificAlgebraicNestedSpecDraw.heights model root p.input (step T) hp hm hm0 hml (mono hmT hbase) (hT.trans hbase) H K bits j⟩
  have hr:=PlayerSpecificNestedRestoreSourceCost.cost root p.focus (PlayerSpecificNestedSpecDrawExecution.run model root p.input H K bits).1 U
    hml (mono hmT hTU) (mono he hTU) hy
  rw [PlayerSpecificNestedTerminalDrawExecution.price_equation]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hc hd) hr) 2

theorem same_return_and_cost (root : Candidate) (a : Input) (T H K : ℕ) (bits : Fin ((17*H+K)+K) → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo<root.interval.hi) (hT : 2≤T) (ha : Fits root a T) :
    (PlayerSpecificNestedTerminalDrawExecution.run RationalCostModel.schoolbook root a H K bits).1=
      PlayerSpecificAlgebraicNestedTerminalDraw.draw RationalCostModel.schoolbook root a H K bits ∧
    (PlayerSpecificNestedTerminalDrawExecution.run RationalCostModel.schoolbook root a H K bits).2≤work T H K :=
  ⟨PlayerSpecificNestedTerminalDrawExecution.value _ root a H K bits,cost root a T H K bits hm hm0 hml hmT he hv hT ha⟩

end Blotto.PlayerSpecificNestedTerminalDrawSourceCost
