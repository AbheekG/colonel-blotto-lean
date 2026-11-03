import Blotto.PlayerSpecificBreakpointConstruction

/-! Rational breakpoint acceptance executes three exact substitutions,
the two endpoint gates and every comparison. It does not invoke algebraic
root isolation or a real-number primitive. -/
namespace Blotto.PlayerSpecificBreakpointTestExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalCells PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (c : Cell) (b q : ℚ) : Bool×Trace :=
  let polynomial:=PlayerSpecificCubicConstruction.run c b
  let tests:=PlayerSpecificCellTestConstruction.run c
  let root:=PlayerSpecificDenseExecution.evaluate polynomial.1 q
  let first:=PlayerSpecificDenseExecution.evaluate tests.1.first q
  let second:=PlayerSpecificDenseExecution.evaluate tests.1.second q
  let positive:=PlayerSpecificRationalTrace.compare q 0
  let lower:=PlayerSpecificRationalTrace.compare c.lower q
  let zero:=equalZero root.1
  let firstPass:=PlayerSpecificRationalTrace.compare 0 first.1
  let secondPass:=PlayerSpecificRationalTrace.compare 0 second.1
  let accepted:=(!positive.1 && lower.1 && zero.1 && firstPass.1 && secondPass.1)
  (accepted,polynomial.2++tests.2++root.2++first.2++second.2++positive.2++lower.2++zero.2++firstPass.2++secondPass.2++
    copyRow [b,q]++[.control (if accepted then 1 else 0),.control 5])

theorem gates (c : Cell) (b q : ℚ) (hb : b≠0) :
    (0≤evaluate (PlayerSpecificAlgebraicCellTests.firstGate c) q ∧
      0≤evaluate (PlayerSpecificAlgebraicCellTests.secondGate c) q) ↔ PlayerSpecificRationalBreakpoint.passes c b q := by
  have hg:=PlayerSpecificAlgebraicCellTests.gates_iff c b hb (q:ℝ)
  rw [PlayerSpecificSturmVariations.evaluate_cast,PlayerSpecificSturmVariations.evaluate_cast] at hg
  constructor
  · intro h
    have hr : (0:ℝ)≤(evaluate (PlayerSpecificAlgebraicCellTests.firstGate c) q:ℝ) ∧
        (0:ℝ)≤(evaluate (PlayerSpecificAlgebraicCellTests.secondGate c) q:ℝ) := by exact_mod_cast h
    exact (PlayerSpecificRationalBreakpoint.passes_cast c b q).mpr (hg.mp hr)
  · intro h
    have hr:=hg.mpr ((PlayerSpecificRationalBreakpoint.passes_cast c b q).mp h)
    exact_mod_cast hr

theorem value (c : Cell) (b q : ℚ) (hb : b≠0) :
    (run c b q).1=true ↔ 0<q ∧ c.lower≤q ∧ evaluate (cubic c.state.coefficients b) q=0 ∧
      PlayerSpecificRationalBreakpoint.passes c b q := by
  have hv:=PlayerSpecificCellTestConstruction.values c
  simp only [run,PlayerSpecificCubicConstruction.value,hv.2.2.2.1,hv.2.2.2.2,
    PlayerSpecificDenseExecution.evaluate_value,PlayerSpecificRationalTrace.compare,equalZero,
    Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,decide_eq_true_eq,not_le]
  rw [←gates c b q hb]
  tauto

end Blotto.PlayerSpecificBreakpointTestExecution
