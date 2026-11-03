import Blotto.BinaryArithmeticAllocation

/-! Addition's established complete-width reservation and multiplication's
reached additions accompany the actual allocation producer. Data are computed
once; work, lengths and allocation observers are erasable source instruments.
Their native evaluation and physical allocator realization remain separate. -/

namespace Blotto.BinaryArithmeticMeasured
set_option autoImplicit false

def add (first second : List Bool) : (List Bool × ℕ) × ℕ :=
  let result := BinaryArithmeticAllocation.addWithAllocation first second
  (result,22*(max first.length second.length+1))

theorem add_erases (first second : List Bool) :
    (add first second).1 = BinaryArithmeticAllocation.addWithAllocation first second := rfl

theorem add_data (first second : List Bool) :
    (add first second).1.1 = BinaryAddition.add first second := by
  simp only [add,BinaryArithmeticAllocation.addWithAllocation_refines]

theorem add_work (first second : List Bool) :
    (add first second).2 = BinaryAddition.bitWork first second := by
  simp only [add,BinaryAddition.bitWork,BinaryAddition.visits_eq]
  omega

def multiply : List Bool → List Bool → (List Bool × ℕ) × ℕ
  | [],_ => (([],1),1)
  | bit::rest,other =>
      let earlier := multiply rest other
      let shifted := false::earlier.1.1
      if bit then
        let added := add other shifted
        ((added.1.1,earlier.1.2+3+added.1.2),earlier.2+3+added.2)
      else ((shifted,earlier.1.2+3),earlier.2+3)

theorem multiply_erases (first second : List Bool) :
    (multiply first second).1 = BinaryArithmeticAllocation.multiplyWithAllocation first second := by
  induction first with
  | nil => rfl
  | cons bit rest ih => cases bit <;>
      simp only [multiply,BinaryArithmeticAllocation.multiplyWithAllocation,Bool.false_eq_true,ite_false,ite_true,
        add_erases,ih]

theorem multiply_data (first second : List Bool) :
    (multiply first second).1.1 = BinaryMultiplication.multiply first second := by
  rw [multiply_erases,BinaryArithmeticAllocation.multiplyWithAllocation_refines]

theorem multiply_work (first second : List Bool) :
    (multiply first second).2 = BinaryMultiplication.work first second := by
  induction first with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [multiply,BinaryMultiplication.work,
      Bool.false_eq_true,ite_false,ite_true,add_work,multiply_data,ih,Nat.add_zero]

end Blotto.BinaryArithmeticMeasured
