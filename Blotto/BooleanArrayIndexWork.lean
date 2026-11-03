import Blotto.BooleanArrayIndexEnumeration

/-! Measured Boolean index production follows actual carries, with no
numeric index assembly. Amortized work includes every visited carry cell. -/
namespace Blotto.BooleanArrayIndexWork
open BinaryCarryCounter

def carryWithWork : List Bool → List Bool × ℕ
  | [] => ([true],4)
  | false::rest => (true::rest,4)
  | true::rest => let next := carryWithWork rest; (false::next.1,next.2+4)

theorem carry_state (bits : List Bool) : (carryWithWork bits).1 = increment bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [carryWithWork,increment,ih]

theorem carry_work (bits : List Bool) : (carryWithWork bits).2 = 4*carryCells bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [carryWithWork,carryCells,ih] <;> omega

def loopWithWork {α : Type*} : List α → List Bool → (List (List Bool) × List Bool) × ℕ
  | [],counter => (([],counter),4)
  | _::rest,counter =>
      let advanced := carryWithWork counter
      let next := loopWithWork rest advanced.1
      ((counter::next.1.1,next.1.2),advanced.2+next.2+8)

theorem loop_state {α : Type*} (ruler : List α) (counter : List Bool) :
    (loopWithWork ruler counter).1 = (BooleanArrayIndexEnumeration.loopWithTrace ruler counter).1 := by
  induction ruler generalizing counter with
  | nil => rfl
  | cons item rest ih =>
      simp only [loopWithWork,BooleanArrayIndexEnumeration.loopWithTrace,carry_state,
        BinaryWordStoreLifetime.carryWithTrace_erases,ih]

theorem loop_work {α : Type*} (ruler : List α) (counter : List Bool) :
    (loopWithWork ruler counter).2 = 4*countCarryCells ruler counter+8*ruler.length+4 := by
  induction ruler generalizing counter with
  | nil => rfl
  | cons item rest ih =>
      simp only [loopWithWork,carry_state,carry_work,ih,countCarryCells,List.length_cons]
      omega

def enumerateWithWork {α : Type*} (ruler : List α) : List (List Bool) × ℕ :=
  let built := loopWithWork ruler []
  (built.1.1,built.2)

theorem enumerate_state {α : Type*} (ruler : List α) :
    (enumerateWithWork ruler).1 = (BooleanArrayIndexEnumeration.enumerateWithTrace ruler).1 := by
  simp only [enumerateWithWork,BooleanArrayIndexEnumeration.enumerateWithTrace,loop_state]

theorem enumerate_work {α : Type*} (ruler : List α) : (enumerateWithWork ruler).2 ≤ 16*ruler.length+4 := by
  have h := countCarryCells_bound ruler []
  change countCarryCells ruler [] ≤ 2*ruler.length at h
  simp only [enumerateWithWork,loop_work]
  omega

end Blotto.BooleanArrayIndexWork
