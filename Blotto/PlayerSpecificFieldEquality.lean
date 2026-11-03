import Blotto.PlayerSpecificFieldCombinationContract

/-! Actual exact equality computes the reduced difference and executes its
priced normalized zero test. Every caller/control cost is included. -/
namespace Blotto.PlayerSpecificFieldEquality
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

def widthCoefficient : ℕ := PlayerSpecificFieldCombinationCost.widthCoefficient+2000000
def width (m a b : Data) : ℕ := widthCoefficient*(PlayerSpecificFieldCombinationContract.inputHeight m a b+1)
def run (model : RationalCostModel) (m a b : Data) : Bool×ℕ :=
  let difference:=PlayerSpecificFieldCombination.run true m a b
  let zero:=PlayerSpecificAlgebraicZeroExecution.run model difference.1
  (zero.1,price model difference.2+zero.2+price model [.control 1])

theorem exact_value (model : RationalCostModel) (m a b : Data) (hm : Normalized m)
    (hirr : Irreducible (semantics m)) (hml : m.length≤4) (x : ℝ) (hx : realEvaluate m x=0) :
    (run model m a b).1=true ↔ realEvaluate a x=realEvaluate b x := by
  have hm0 : m≠[] := by intro h; exact hirr.ne_zero (by rw [h]; rfl)
  have hr:=PlayerSpecificFieldCombination.reduced true m a b hm hm0
  have hz:=(PlayerSpecificAlgebraicZeroExecution.actual_contract model m (PlayerSpecificFieldCombination.run true m a b).1 hm hirr hml hr x hx).1
  change (PlayerSpecificAlgebraicZeroExecution.run model (PlayerSpecificFieldCombination.run true m a b).1).1=true ↔ _
  rw [hz,PlayerSpecificFieldCombination.real_value true m a b x hx]
  simp only [ite_true,sub_eq_zero]

theorem encoded_profile (H E : ℕ) (hE : E≤3*(1+2*(100000*(H+1)))+1) : 2*E+32≤2000000*(H+1) := by
  nlinarith only [hE]

theorem source_cost (model : RationalCostModel) (m a b : Data) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (hal : a.length≤3) (hbl : b.length≤3) :
    (run model m a b).2≤201000000*model.rat (width m a b) := by
  let H:=PlayerSpecificFieldCombinationContract.inputHeight m a b
  have hi:=PlayerSpecificFieldCombinationContract.input_heights m a b
  have hr:=PlayerSpecificFieldCombination.reduced true m a b hm hm0
  have hlen : (PlayerSpecificFieldCombination.run true m a b).1.length≤3 := by have hl:=hr.2; omega
  have hh:=PlayerSpecificFieldCombination.bounds true m a b H hi.1 hi.2.1 hi.2.2.1 hml hal hbl
  have hc:=PlayerSpecificFieldCombinationCost.run_cost model true m a b hm hm0 hml H hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 hal hbl
  have hcw : PlayerSpecificFieldCombinationCost.width H≤width m a b :=
    Nat.mul_le_mul_right _ (by unfold widthCoefficient; omega)
  have hcp:=hc.trans (Nat.mul_le_mul_left 200000000 (model.monotone hcw))
  have he:=inputHeight_le hh
  have hem:=Nat.mul_le_mul_right (1+2*(100000*(H+1))) hlen
  have he' : PlayerSpecificRationalMagnitude.inputHeight (PlayerSpecificFieldCombination.run true m a b).1≤
      3*(1+2*(100000*(H+1)))+1 := he.trans (Nat.add_le_add_right hem 1)
  have hz:=PlayerSpecificAlgebraicZeroExecution.source_cost model (PlayerSpecificFieldCombination.run true m a b).1 hlen
  have hzw : 2*PlayerSpecificRationalMagnitude.inputHeight (PlayerSpecificFieldCombination.run true m a b).1+32≤width m a b :=
    (encoded_profile H _ he').trans (Nat.mul_le_mul_right _ (by unfold widthCoefficient; omega))
  have hzp:=hz.trans (Nat.mul_le_mul_left 100 (model.monotone hzw))
  have hW : 32≤width m a b := by unfold width widthCoefficient; nlinarith
  have hctrl:=event_price model (width m a b) (by omega) (.control 1) ((control_width 1).trans (by omega))
  change price model [.control 1]≤3*model.rat (width m a b) at hctrl
  rw [run]
  dsimp only
  nlinarith only [hcp,hzp,hctrl]

theorem actual_contract (model : RationalCostModel) (m a b : Data) (hm : Normalized m)
    (hirr : Irreducible (semantics m)) (hml : m.length≤4) (hal : a.length≤3) (hbl : b.length≤3)
    (x : ℝ) (hx : realEvaluate m x=0) :
    ((run model m a b).1=true ↔ realEvaluate a x=realEvaluate b x) ∧
      (run model m a b).2≤201000000*model.rat (width m a b) := by
  have hm0 : m≠[] := by intro h; exact hirr.ne_zero (by rw [h]; rfl)
  exact ⟨exact_value model m a b hm hirr hml x hx,source_cost model m a b hm hm0 hml hal hbl⟩

end Blotto.PlayerSpecificFieldEquality
