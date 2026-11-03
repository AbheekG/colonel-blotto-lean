import Blotto.BinaryPhysicalBuildAllowanceLifetime
import Blotto.BinarySeedCursorMeasured

/-! Actual full-adder, schoolbook multiplication and node-word construction
return old data/trace with work in one execution. The adder includes its actual
final reversal: the per-bit charge plus reversal gives the preceding `bitWork`
exactly. Native work/trace observer arithmetic and reference/GC joins remain. -/
namespace Blotto.BinaryBuildAllowanceArithmeticMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 2500000

def addLoop : List Bool → List Bool → Bool → List Bool → (List Bool × Trace) × ℕ
  | [],[],carry,acc =>
      let reversed := BinarySeedCursorMeasured.reverse (if carry then true::acc else acc) []
      ((reversed.1.1,wrapList (if carry then 1 else 0) 8 1 [reversed.1.2]),
        reversed.2+(if carry then 16 else 20))
  | a::rest,[],carry,acc =>
      let later := addLoop rest [] (BinaryAddition.nextCarry a false carry) (BinaryAddition.sumBit a false carry::acc)
      ((later.1.1,wrapList 1 8 2 [later.1.2]),later.2+18)
  | [],b::rest,carry,acc =>
      let later := addLoop [] rest (BinaryAddition.nextCarry false b carry) (BinaryAddition.sumBit false b carry::acc)
      ((later.1.1,wrapList 1 8 2 [later.1.2]),later.2+18)
  | a::as,b::bs,carry,acc =>
      let later := addLoop as bs (BinaryAddition.nextCarry a b carry) (BinaryAddition.sumBit a b carry::acc)
      ((later.1.1,wrapList 1 8 2 [later.1.2]),later.2+18)

theorem addLoop_erases (a b : List Bool) (carry : Bool) (acc : List Bool) :
    (addLoop a b carry acc).1 = BinaryPhysicalBuildAllowanceLifetime.addLoopWithTrace a b carry acc := by
  induction a generalizing b carry acc with
  | nil =>
      induction b generalizing carry acc with
      | nil => simp only [addLoop,BinaryPhysicalBuildAllowanceLifetime.addLoopWithTrace,BinarySeedCursorMeasured.reverse_erases]
      | cons bit rest ih => simp only [addLoop,BinaryPhysicalBuildAllowanceLifetime.addLoopWithTrace,ih]
  | cons bit rest ih => cases b with
    | nil => simp only [addLoop,BinaryPhysicalBuildAllowanceLifetime.addLoopWithTrace,ih]
    | cons other tail => simp only [addLoop,BinaryPhysicalBuildAllowanceLifetime.addLoopWithTrace,ih]

theorem addLoop_work (a b : List Bool) (carry : Bool) (acc : List Bool) :
    (addLoop a b carry acc).2 = 22*(max a.length b.length+1)+4*acc.length := by
  induction a generalizing b carry acc with
  | nil =>
      induction b generalizing carry acc with
      | nil =>
          simp only [addLoop,BinarySeedCursorMeasured.reverse_work,BinaryMidpointTapeLifetime.reverse_work]
          cases carry <;> simp only [Bool.false_eq_true,ite_false,ite_true,List.length_nil,List.length_cons,Nat.max_self] <;> omega
      | cons bit rest ih =>
          have h := ih (BinaryAddition.nextCarry false bit carry) (BinaryAddition.sumBit false bit carry::acc)
          simp only [addLoop,List.length_cons,List.length_nil,Nat.zero_max] at h ⊢
          omega
  | cons bit rest ih => cases b with
    | nil =>
        have h := ih [] (BinaryAddition.nextCarry bit false carry) (BinaryAddition.sumBit bit false carry::acc)
        simp only [addLoop,List.length_cons,List.length_nil,Nat.max_zero] at h ⊢
        omega
    | cons other tail =>
        have h := ih tail (BinaryAddition.nextCarry bit other carry) (BinaryAddition.sumBit bit other carry::acc)
        simp only [addLoop,List.length_cons] at h ⊢
        omega

def add (a b : List Bool) : (List Bool × Trace) × ℕ := addLoop a b false []

theorem add_erases (a b : List Bool) : (add a b).1 = BinaryPhysicalBuildAllowanceLifetime.addWithTrace a b :=
  addLoop_erases a b false []

theorem add_data (a b : List Bool) : (add a b).1.1 = BinaryAddition.add a b := by
  rw [add_erases,BinaryPhysicalBuildAllowanceLifetime.addWithTrace_erases]

theorem add_work (a b : List Bool) : (add a b).2 = BinaryAddition.bitWork a b := by
  simp only [add,addLoop_work,List.length_nil,mul_zero,Nat.add_zero,BinaryAddition.bitWork,BinaryAddition.visits_eq]
  omega

def multiply : List Bool → List Bool → (List Bool × Trace) × ℕ
  | [],_ => (([],wrap 8 1 []),1)
  | bit::rest,other =>
      let earlier := multiply rest other
      let shifted := false::earlier.1.1
      if bit then
        let added := add other shifted
        ((added.1.1,wrapList 1 16 2 [earlier.1.2,added.1.2]),earlier.2+3+added.2)
      else ((shifted,wrapList 1 8 2 [earlier.1.2]),earlier.2+3)

theorem multiply_erases (a b : List Bool) :
    (multiply a b).1 = BinaryPhysicalBuildAllowanceLifetime.multiplyWithTrace a b := by
  induction a with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [multiply,BinaryPhysicalBuildAllowanceLifetime.multiplyWithTrace,
      Bool.false_eq_true,ite_false,ite_true,add_erases,ih]

theorem multiply_data (a b : List Bool) : (multiply a b).1.1 = BinaryMultiplication.multiply a b := by
  rw [multiply_erases,BinaryPhysicalBuildAllowanceLifetime.multiplyWithTrace_erases]

theorem multiply_work (a b : List Bool) : (multiply a b).2 = BinaryMultiplication.work a b := by
  induction a with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [multiply,BinaryMultiplication.work,
      Bool.false_eq_true,ite_false,ite_true,add_work,multiply_data,ih,Nat.add_zero]

def nodes : List Bool → (List Bool × Trace) × ℕ
  | [] => (([true],wrapList 1 8 1 []),2)
  | _::rest =>
      let later := nodes rest
      ((true::later.1.1,wrapList 1 8 1 [later.1.2]),later.2+2)

theorem nodes_erases (ruler : List Bool) :
    (nodes ruler).1 = BinaryPhysicalBuildAllowanceLifetime.nodesWordWithTrace ruler := by
  induction ruler with
  | nil => rfl
  | cons bit rest ih => simp only [nodes,BinaryPhysicalBuildAllowanceLifetime.nodesWordWithTrace,ih]

theorem nodes_data (ruler : List Bool) : (nodes ruler).1.1 = (BinaryPhysicalBuildAllowance.nodesWordWithWork ruler).1 := by
  rw [nodes_erases,BinaryPhysicalBuildAllowanceLifetime.nodesWordWithTrace_erases,
    BinaryPhysicalBuildAllowance.nodesWordWithWork_erases]

theorem nodes_work (ruler : List Bool) : (nodes ruler).2 = (BinaryPhysicalBuildAllowance.nodesWordWithWork ruler).2 := by
  induction ruler with
  | nil => rfl
  | cons bit rest ih => simp only [nodes,BinaryPhysicalBuildAllowance.nodesWordWithWork,ih]

end Blotto.BinaryBuildAllowanceArithmeticMeasured
