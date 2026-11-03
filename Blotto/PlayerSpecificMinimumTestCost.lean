import Blotto.PlayerSpecificMinimumContract

/-! Complete source cost of the actual minimum-length comparison scan.
Difference construction, root sign calls, returned copies and scan control
words are all included. -/
namespace Blotto.PlayerSpecificMinimumTestCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificSturmVariations PlayerSpecificRationalTrace PlayerSpecificIsolationState
set_option autoImplicit false
set_option maxHeartbeats 2500000

def widthCoefficient : ℕ := 65*PlayerSpecificPolynomialSignBudget.widthCoefficient+1000
def width (H : ℕ) : ℕ := widthCoefficient*(H+1)
def testCoefficient : ℕ := 65*PlayerSpecificPolynomialSignCost.workCoefficient+1000000
def scanCoefficient : ℕ := testCoefficient+1000

theorem width_large (H : ℕ) : 128*(H+1)≤width H :=
  Nat.mul_le_mul_right _ (by unfold widthCoefficient; omega)

theorem row_copy (model : RationalCostModel) (a : Data) (H : ℕ) (ha : HasHeight a H) (hal : a.length≤21) :
    price model (copyRow a)≤66*model.rat (width H) := by
  have hw:=width_large H
  exact PlayerSpecificExtendedCopyCost.row_cost model a H (width H) ha hal (by omega) (by omega)

theorem control (model : RationalCostModel) (n H : ℕ) (hn : n≤H+2) :
    price model [.control n]≤3*model.rat (width H) := by
  have hw:=width_large H
  exact event_price model (width H) (by omega) (.control n) ((control_width n).trans (by omega))

theorem test_cost (model : RationalCostModel) (m a : Data) (node : Interval) (q : ℚ) (H : ℕ)
    (hm : Normalized m) (hm0 : m≠[]) (hml : m.length≤4) (hal : a.length≤3)
    (hmH : HasHeight m H) (ha : HasHeight a H) (he : HasHeight [node.lo,node.hi] H)
    (hq : RationalHeight q H) (hH : 1≤H) (hv : node.lo<node.hi) :
    (PlayerSpecificMinimumTest.test model m a node q).2≤testCoefficient*(H+1)*model.rat (width H) := by
  have hqRow:=cons_height hq (nil_height H)
  have hd:=PlayerSpecificDenseOperationCost.subtract_cost model a [q] H 4 ha hqRow hH (by omega) (by simp)
  rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at hd
  have hd':=hd.trans (Nat.mul_le_mul_left 375000 (model.monotone
    (show 40*H+64≤width H by have hw:=width_large H; omega)))
  have hdiff : HasHeight (PlayerSpecificDenseExecution.subtract a [q]).1 (2*H+1) := by
    rw [PlayerSpecificDenseExecution.subtract_value]
    simpa only [two_mul] using subtract_height ha hqRow
  have hdiffLen : (PlayerSpecificDenseExecution.subtract a [q]).1.length≤4 := by
    rw [PlayerSpecificDenseExecution.subtract_value,subtract,add_length,scale_length]
    simp only [List.length_cons,List.length_nil]
    omega
  have hinput:=PlayerSpecificCandidateTestBudget.encoded_input m _ node (2*H+1)
    (mono hmH (by omega)) hdiff (mono he (by omega)) hml hdiffLen
  have hinput' : PlayerSpecificPolynomialSignBudget.inputHeight m
      (PlayerSpecificDenseExecution.subtract a [q]).1 node+1≤65*(H+1) := by omega
  have hs:=PlayerSpecificPolynomialSignCost.run_cost model m (PlayerSpecificDenseExecution.subtract a [q]).1 node hm hm0 hml hdiffLen hv
  have hwork:=Nat.mul_le_mul_left PlayerSpecificPolynomialSignCost.workCoefficient hinput'
  have hwidth : PlayerSpecificPolynomialSignBudget.width (PlayerSpecificPolynomialSignBudget.inputHeight m
      (PlayerSpecificDenseExecution.subtract a [q]).1 node)≤width H := by
    have hh:=Nat.mul_le_mul_left PlayerSpecificPolynomialSignBudget.widthCoefficient hinput'
    have hc:=Nat.mul_le_mul_right (H+1)
      (show 65*PlayerSpecificPolynomialSignBudget.widthCoefficient≤widthCoefficient by unfold widthCoefficient; omega)
    unfold PlayerSpecificPolynomialSignBudget.width width
    nlinarith only [hh,hc]
  have hs':=hs.trans (Nat.mul_le_mul hwork (model.monotone hwidth))
  have hmcopy:=row_copy model m H hmH (by omega)
  have hacopy:=row_copy model a H ha (by omega)
  have heq:=cons_height (head_height he) (cons_height (head_height (tail_height he)) hqRow)
  have hecopy:=row_copy model [node.lo,node.hi,q] H heq (by simp)
  have hc:=control model 1 H (by omega)
  simp only [PlayerSpecificMinimumTest.test,price_append]
  unfold testCoefficient
  nlinarith only [hd',hs',hmcopy,hacopy,hecopy,hc]

theorem scan_cost (model : RationalCostModel) (m : Data) (node : Interval) (q : ℚ) (rows : List Data) (H : ℕ)
    (hm : Normalized m) (hm0 : m≠[]) (hml : m.length≤4) (hmH : HasHeight m H)
    (he : HasHeight [node.lo,node.hi] H) (hq : RationalHeight q H) (hH : 1≤H)
    (hv : node.lo<node.hi) (hlen : rows.length≤H)
    (hrows : ∀ a∈rows,HasHeight a H ∧ a.length≤3) :
    (PlayerSpecificMinimumTest.all model m node q rows).2≤
      scanCoefficient*(rows.length+1)*(H+1)*model.rat (width H) := by
  have hcopy:=row_copy model [q] H (cons_height hq (nil_height H)) (by simp)
  have hzero:=control model 0 H (by omega)
  have hunit:=Nat.mul_le_mul_right (model.rat (width H)) (show 1≤H+1 by omega)
  induction rows with
  | nil =>
    simp only [PlayerSpecificMinimumTest.all,price_append,List.length_nil]
    have hp : 1≤H+1 := by omega
    have hh:=Nat.mul_le_mul_right (model.rat (width H)) hp
    unfold scanCoefficient testCoefficient
    nlinarith only [hcopy,hzero,hh]
  | cons a rows ih =>
    have ht:=test_cost model m a node q H hm hm0 hml (hrows a List.mem_cons_self).2 hmH
      (hrows a List.mem_cons_self).1 he hq hH hv
    have hi:=ih (by simp only [List.length_cons] at hlen; omega)
      (fun a ha => hrows a (List.mem_cons_of_mem _ ha))
    have hc:=control model (rows.length+1) H (by simp only [List.length_cons] at hlen; omega)
    have hone:=control model 1 H (by omega)
    simp only [PlayerSpecificMinimumTest.all]
    split <;> dsimp only
    · simp only [price,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at *
      simp only [List.length_cons]
      unfold scanCoefficient at *
      nlinarith only [ht,hi,hcopy,hc,hone,hunit]
    · simp only [price,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at *
      simp only [List.length_cons]
      have hp : 1≤rows.length+2 := by omega
      have hmul:=Nat.mul_le_mul_right (testCoefficient*(H+1)*model.rat (width H)) hp
      unfold scanCoefficient
      nlinarith only [ht,hcopy,hc,hzero,hmul,hunit]

end Blotto.PlayerSpecificMinimumTestCost
