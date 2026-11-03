import Blotto.PlayerSpecificBreakpointTestExecution

/-! The full rational breakpoint predicate has a constant number of
operand-priced rational operations at a linear original-cell width. -/
namespace Blotto.PlayerSpecificBreakpointTestCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def width (H : ℕ) : ℕ := 2048*(H+1)

theorem evaluate_cost (model : RationalCostModel) (p : Data) (q : ℚ) (H : ℕ)
    (hp : HasHeight p (4*H+4)) (hq : RationalHeight q H) (hlen : p.length≤4) :
    price model (PlayerSpecificDenseExecution.evaluate p q).2≤141*model.rat (width H) := by
  have he:=PlayerSpecificHornerTraceCost.evaluate_cost model p q (4*H+4) 4 hp (hq.mono (by omega)) hlen
  have hw : PlayerSpecificHornerTraceCost.width (4*H+4) 4≤width H := by
    unfold PlayerSpecificHornerTraceCost.width PlayerSpecificHornerTraceCost.valueHeight width
    omega
  exact he.trans (Nat.mul_le_mul (by omega) (model.monotone hw))

theorem evaluated_height (p : Data) (q : ℚ) (H : ℕ) (hp : HasHeight p (4*H+4))
    (hq : RationalHeight q H) (hlen : p.length≤4) :
    RationalHeight (PlayerSpecificDenseExecution.evaluate p q).1 (40*(H+1)) := by
  rw [PlayerSpecificDenseExecution.evaluate_value]
  have hh:=evaluate_height hp (hq.mono (show H≤4*H+4 by omega))
  have hm:=Nat.mul_le_mul_left ((4*H+4)+(4*H+4)+1) hlen
  exact hh.mono (by omega)

theorem run_cost (model : RationalCostModel) (c : Cell) (b q : ℚ) (H : ℕ)
    (hc : CellHeight c H) (hb : RationalHeight b H) (hq : RationalHeight q H) (hH : 1≤H) :
    price model (PlayerSpecificBreakpointTestExecution.run c b q).2≤4000*model.rat (width H) := by
  let polynomial:=PlayerSpecificCubicConstruction.run c b
  let tests:=PlayerSpecificCellTestConstruction.run c
  have hpoly : HasHeight polynomial.1 (4*H+4) := by
    rw [PlayerSpecificCubicConstruction.value]
    exact mono (PlayerSpecificCellPolynomialHeights.cubic_height c b H hc hb) (by omega)
  have hpLen : polynomial.1.length≤4 := by rw [PlayerSpecificCubicConstruction.value]; simp [cubic]
  have htests:=PlayerSpecificCandidateTestBudget.tests_bounds c H hc hH
  have hfirst : HasHeight tests.1.first (4*H+4) := htests.2.2.2.1.1
  have hsecond : HasHeight tests.1.second (4*H+4) := htests.2.2.2.2.1
  have hfirstLen : tests.1.first.length≤4 := htests.2.2.2.1.2
  have hsecondLen : tests.1.second.length≤4 := htests.2.2.2.2.2
  have hroot:=evaluate_cost model polynomial.1 q H hpoly hq hpLen
  have hfirstEval:=evaluate_cost model tests.1.first q H hfirst hq hfirstLen
  have hsecondEval:=evaluate_cost model tests.1.second q H hsecond hq hsecondLen
  have hhroot:=evaluated_height polynomial.1 q H hpoly hq hpLen
  have hhfirst:=evaluated_height tests.1.first q H hfirst hq hfirstLen
  have hhsecond:=evaluated_height tests.1.second q H hsecond hq hsecondLen
  have hW : 32≤width H := by unfold width; omega
  have word (a : ℚ) (ha : RationalHeight a (40*(H+1))) : rationalWordWidth a≤width H :=
    (rationalWordWidth_of_height ha).trans (by unfold width; omega)
  have hzero:=word 0 (zero_height.mono (by omega))
  have hqword:=word q (hq.mono (by omega))
  have hlower:=word c.lower (hc.2.1.mono (by omega))
  have comparison (a d : ℚ) (ha : rationalWordWidth a≤width H) (hd : rationalWordWidth d≤width H) :
      price model (PlayerSpecificRationalTrace.compare a d).2≤12*model.rat (width H) := by
    have hp:=price_bound model (width H) (by omega) _ (compare_fits _ a d ha hd (by omega))
    rwa [compare_length] at hp
  have hpositive:=comparison q 0 hqword hzero
  have hlow:=comparison c.lower q hlower hqword
  have hfp:=comparison 0 _ hzero (word _ hhfirst)
  have hsp:=comparison 0 _ hzero (word _ hhsecond)
  have hz:=price_bound model (width H) (by omega) _ (equalZero_fits _ _ (word _ hhroot) hzero (by omega))
  rw [equalZero_length] at hz
  have hpolyc:=PlayerSpecificCubicConstruction.run_cost model c b H hc hb hH
  have htestc:=PlayerSpecificCellTestConstructionCost.run_cost model c H hc hH
  have hsmall : 128*(H+1)≤width H := by unfold width; omega
  have hpolycp:=hpolyc.trans (Nat.mul_le_mul_left 1000 (model.monotone hsmall))
  have htestcp:=htestc.trans (Nat.mul_le_mul_left 1000 (model.monotone hsmall))
  have hcopy:=PlayerSpecificExtendedCopyCost.row_cost model [b,q] H (width H)
    (cons_height hb (cons_height hq (nil_height _))) (by simp) (by unfold width; omega) hW
  have controls (accepted : Bool) : price model [.control (if accepted then 1 else 0),.control 5]≤6*model.rat (width H) := by
    have hf : Fits (width H) [.control (if accepted then 1 else 0),.control 5] := by
      intro e he
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl
      · exact (PlayerSpecificRationalTrace.control_width _).trans (by cases accepted <;> simp <;> omega)
      · exact (PlayerSpecificRationalTrace.control_width 5).trans (by omega)
    exact price_bound model (width H) (by omega) _ hf
  have hcontrols:=controls
    (!((PlayerSpecificRationalTrace.compare q 0).1) && (PlayerSpecificRationalTrace.compare c.lower q).1 &&
      (equalZero (PlayerSpecificDenseExecution.evaluate polynomial.1 q).1).1 &&
      (PlayerSpecificRationalTrace.compare 0 (PlayerSpecificDenseExecution.evaluate tests.1.first q).1).1 &&
      (PlayerSpecificRationalTrace.compare 0 (PlayerSpecificDenseExecution.evaluate tests.1.second q).1).1)
  rw [PlayerSpecificBreakpointTestExecution.run]
  dsimp only
  simp only [price_append]
  nlinarith only [hroot,hfirstEval,hsecondEval,hpositive,hlow,hfp,hsp,hz,hpolycp,htestcp,hcopy,hcontrols]

end Blotto.PlayerSpecificBreakpointTestCost
