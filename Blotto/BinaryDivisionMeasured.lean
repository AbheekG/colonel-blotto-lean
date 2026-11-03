import Blotto.BinaryDivisionAllocation
import Blotto.BinaryBooleanPrimitiveLifetime

/-! Restoring division consumes the actual borrow result and selected residual
once per digit. Closed width/visit reservations reproduce the existing source
work. Allocation and trace observers, including retained buffer reservations,
are ghost instruments; native observer arithmetic and allocator costs are open. -/

namespace Blotto.BinaryDivisionMeasured
open BinarySeedPreparationSpace
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem borrow_visits (first second : List Bool) :
    BinaryBorrowWord.visits first second = min first.length second.length+1 := by
  induction first generalizing second with
  | nil => cases second <;> rfl
  | cons bit rest ih => cases second with
    | nil => rfl
    | cons other tail => simp only [BinaryBorrowWord.visits,List.length_cons,ih]; omega

theorem drop_visits (bits : List Bool) : BinaryWordHighBit.visits bits = max 1 bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases rest with
    | nil => rfl
    | cons next tail => simp only [BinaryWordHighBit.visits,List.length_cons] at ih ⊢; omega

def step (incoming : Bool) (remainder divisor : List Bool) : ((Bool × List Bool) × ℕ) × ℕ :=
  let shifted := incoming::remainder
  let padded := divisor++[false]
  let difference := BinaryDivisionAllocation.borrowWithAllocation shifted padded false []
  let chosen := if difference.1.2 then shifted else difference.1.1
  let dropped := BinaryDivisionAllocation.dropWithAllocation chosen []
  (((!difference.1.2,dropped.1),1+(divisor.length+1)+difference.2+dropped.2+4),
    2+(divisor.length+1)+8*(remainder.length+1)+2*(remainder.length+1)+2*(remainder.length+1)+
      (min shifted.length padded.length+1)+max 1 chosen.length+2*remainder.length+1)

theorem step_erases (incoming : Bool) (remainder divisor : List Bool) :
    (step incoming remainder divisor).1 = BinaryDivisionAllocation.stepWithAllocation incoming remainder divisor := rfl

theorem step_data (incoming : Bool) (remainder divisor : List Bool) :
    (step incoming remainder divisor).1.1 = BinaryDivisionWord.step incoming remainder divisor :=
  BinaryDivisionAllocation.stepWithAllocation_state incoming remainder divisor

theorem step_work (incoming : Bool) (remainder divisor : List Bool) :
    (step incoming remainder divisor).2 = BinaryDivisionWord.bitWork incoming remainder divisor := by
  simp only [step,BinaryDivisionWord.bitWork,borrow_visits,drop_visits,
    BinaryDivisionAllocation.borrowWithAllocation_refines,BinaryDivisionWord.chosenResidual,
    BinaryBorrowWord.subtract]
  rfl

def loop (divisor : List Bool) : List Bool → List Bool → List Bool → ((List Bool × List Bool) × ℕ) × ℕ
  | [],quotient,remainder => (((quotient,remainder),1),1)
  | incoming::rest,quotient,remainder =>
      let digit := step incoming remainder divisor
      let later := loop divisor rest (digit.1.1.1::quotient) digit.1.1.2
      ((later.1.1,digit.1.2+2+later.1.2),digit.2+4+later.2)

theorem loop_erases (divisor bits quotient remainder : List Bool) :
    (loop divisor bits quotient remainder).1 =
      BinaryDivisionAllocation.divisionLoopWithAllocation divisor bits quotient remainder := by
  induction bits generalizing quotient remainder with
  | nil => rfl
  | cons incoming rest ih => simp only [loop,BinaryDivisionAllocation.divisionLoopWithAllocation,step_erases,ih]

theorem loop_work (divisor bits quotient remainder : List Bool) :
    (loop divisor bits quotient remainder).2 = (BinaryLongDivision.loopWithWork divisor bits quotient remainder).2 := by
  induction bits generalizing quotient remainder with
  | nil => rfl
  | cons incoming rest ih => simp only [loop,BinaryLongDivision.loopWithWork,step_data,step_work,ih]

def divide (dividend divisor : List Bool) : ((List Bool × List Bool) × ℕ) × ℕ :=
  let result := loop divisor dividend.reverse [] (BinaryLongDivision.zeroRemainder divisor)
  ((result.1.1,2*dividend.length+divisor.length+result.1.2+2),
    2*dividend.length+2*divisor.length+result.2+2)

theorem divide_erases (dividend divisor : List Bool) :
    (divide dividend divisor).1 = BinaryDivisionAllocation.divideWithAllocation dividend divisor := by
  simp only [divide,BinaryDivisionAllocation.divideWithAllocation,loop_erases]

theorem divide_data (dividend divisor : List Bool) :
    (divide dividend divisor).1.1 = (BinaryLongDivision.divideWithWork dividend divisor).1 := by
  rw [divide_erases,BinaryDivisionAllocation.divideWithAllocation_state,BinaryLongDivision.divideWithWork_refines]

theorem divide_work (dividend divisor : List Bool) :
    (divide dividend divisor).2 = (BinaryLongDivision.divideWithWork dividend divisor).2 := by
  simp only [divide,BinaryLongDivision.divideWithWork,loop_work]

def traced (dividend divisor : List Bool) : ((List Bool × List Bool) × Trace) × ℕ :=
  let result := divide dividend divisor
  ((result.1.1,[.frames (dividend.length+2*divisor.length+16),.arrayAllocation 8,
    .listAllocation (BinaryDivisionAllocation.divideStorage dividend divisor)]),result.2)

theorem traced_erases (dividend divisor : List Bool) :
    (traced dividend divisor).1 = BinaryBooleanPrimitiveLifetime.divideWithTrace dividend divisor := by
  simp only [traced,BinaryBooleanPrimitiveLifetime.divideWithTrace,divide_erases]

theorem traced_data (dividend divisor : List Bool) :
    (traced dividend divisor).1.1 = (BinaryLongDivision.divideWithWork dividend divisor).1 := divide_data dividend divisor

theorem traced_work (dividend divisor : List Bool) :
    (traced dividend divisor).2 = (BinaryLongDivision.divideWithWork dividend divisor).2 := divide_work dividend divisor

theorem traced_bound (dividend divisor : List Bool) :
    (traced dividend divisor).2 ≤ 30*(dividend.length+1)*(divisor.length+1) := by
  rw [traced_work,BinaryLongDivision.divideWithWork_refines]
  exact BinaryLongDivision.bitWork_quadratic dividend divisor

end Blotto.BinaryDivisionMeasured
