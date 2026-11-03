import Blotto.BinaryArithmeticAllocation
import Blotto.BinaryDivisionAllocation

/-! Actual Boolean arithmetic returns its value, allocation, held payload and
source-work reservation together. The old recursive storage observers are not
executed to obtain these fields. Their native arithmetic/reference/GC price is
still a separate model obligation. -/
namespace Blotto.BinaryCompareBitsMeasured
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Result (α : Type) where
  data : α
  allocated : ℕ
  held : ℕ
  work : ℕ

def Result.storage {α : Type} (result : Result α) : ℕ := result.held + result.allocated

def reverse : List Bool → List Bool → List Bool × ℕ
  | [],acc => (acc,2)
  | bit::rest,acc =>
      let later := reverse rest (bit::acc)
      (later.1,later.2+4)

theorem reverse_data (bits acc : List Bool) :
    (reverse bits acc).1 = bits.reverse ++ acc := by
  induction bits generalizing acc with
  | nil => rfl
  | cons bit rest ih => simp [reverse,ih,List.reverse_cons,List.append_assoc]

theorem reverse_work (bits acc : List Bool) : (reverse bits acc).2 = 4*bits.length+2 := by
  induction bits generalizing acc with
  | nil => rfl
  | cons bit rest ih => simp only [reverse,ih,List.length_cons]; omega

def addLoop : List Bool → List Bool → Bool → List Bool → Result (List Bool)
  | [],[],carry,acc =>
      let back := reverse (if carry then true::acc else acc) []
      ⟨back.1,if carry then 1+(acc.length+1) else acc.length,
        acc.length+2,back.2+(if carry then 16 else 20)⟩
  | bit::rest,[],carry,acc =>
      let later := addLoop rest [] (BinaryAddition.nextCarry bit false carry)
        (BinaryAddition.sumBit bit false carry::acc)
      ⟨later.data,2+later.allocated,(bit::rest).length+acc.length+2+later.held,later.work+18⟩
  | [],bit::rest,carry,acc =>
      let later := addLoop [] rest (BinaryAddition.nextCarry false bit carry)
        (BinaryAddition.sumBit false bit carry::acc)
      ⟨later.data,2+later.allocated,(bit::rest).length+acc.length+2+later.held,later.work+18⟩
  | a::as,b::bs,carry,acc =>
      let later := addLoop as bs (BinaryAddition.nextCarry a b carry)
        (BinaryAddition.sumBit a b carry::acc)
      ⟨later.data,2+later.allocated,(a::as).length+(b::bs).length+acc.length+2+later.held,later.work+18⟩

theorem addLoop_data (a b : List Bool) (carry : Bool) (acc : List Bool) :
    (addLoop a b carry acc).data = BinaryAddition.loop a b carry acc := by
  induction a generalizing b carry acc with
  | nil => induction b generalizing carry acc with
    | nil => cases carry <;> simp [addLoop,BinaryAddition.loop,reverse_data]
    | cons bit rest ih => simp only [addLoop,BinaryAddition.loop,ih]
  | cons bit rest ih => cases b with
    | nil => simp only [addLoop,BinaryAddition.loop,ih]
    | cons other tail => simp only [addLoop,BinaryAddition.loop,ih]

theorem addLoop_allocated (a b : List Bool) (carry : Bool) (acc : List Bool) :
    (addLoop a b carry acc).allocated = BinaryArithmeticAllocation.addLoopAllocated a b carry acc := by
  induction a generalizing b carry acc with
  | nil => induction b generalizing carry acc with
    | nil => cases carry <;> simp only [addLoop,BinaryArithmeticAllocation.addLoopAllocated,Bool.false_eq_true,ite_false,ite_true]
    | cons bit rest ih => simp only [addLoop,BinaryArithmeticAllocation.addLoopAllocated,ih]
  | cons bit rest ih => cases b with
    | nil => simp only [addLoop,BinaryArithmeticAllocation.addLoopAllocated,ih]
    | cons other tail => simp only [addLoop,BinaryArithmeticAllocation.addLoopAllocated,ih]

theorem addLoop_held (a b : List Bool) (carry : Bool) (acc : List Bool) :
    (addLoop a b carry acc).held = BinaryArithmeticAllocation.addLoopHeldPayload a b carry acc := by
  induction a generalizing b carry acc with
  | nil => induction b generalizing carry acc with
    | nil => cases carry <;> simp only [addLoop,BinaryArithmeticAllocation.addLoopHeldPayload,Bool.false_eq_true,ite_false,ite_true]
    | cons bit rest ih => simp only [addLoop,BinaryArithmeticAllocation.addLoopHeldPayload,ih]
  | cons bit rest ih => cases b with
    | nil => simp only [addLoop,BinaryArithmeticAllocation.addLoopHeldPayload,ih]
    | cons other tail => simp only [addLoop,BinaryArithmeticAllocation.addLoopHeldPayload,ih]

theorem addLoop_work (a b : List Bool) (carry : Bool) (acc : List Bool) :
    (addLoop a b carry acc).work = 22*(max a.length b.length+1)+4*acc.length := by
  induction a generalizing b carry acc with
  | nil => induction b generalizing carry acc with
    | nil => cases carry <;> simp [addLoop,reverse_work] <;> omega
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

def add (a b : List Bool) : Result (List Bool) := addLoop a b false []

theorem add_data (a b : List Bool) : (add a b).data = BinaryAddition.add a b := addLoop_data a b false []

theorem add_erases (a b : List Bool) :
    ((add a b).data,(add a b).allocated) = BinaryArithmeticAllocation.addWithAllocation a b := by
  rw [BinaryArithmeticAllocation.addWithAllocation_refines]
  exact congrArg₂ Prod.mk (add_data a b) (addLoop_allocated a b false [])

theorem add_storage (a b : List Bool) : (add a b).storage = BinaryArithmeticAllocation.addStorage a b := by
  simp only [Result.storage,add,addLoop_held,addLoop_allocated,BinaryArithmeticAllocation.addStorage]

theorem add_work (a b : List Bool) : (add a b).work = BinaryAddition.bitWork a b := by
  simp only [add,addLoop_work,List.length_nil,mul_zero,Nat.add_zero,BinaryAddition.bitWork,BinaryAddition.visits_eq]
  omega

def multiply : List Bool → List Bool → Result (List Bool)
  | [],other => ⟨[],1,other.length+2,1⟩
  | bit::rest,other =>
      let earlier := multiply rest other
      let shifted := false::earlier.data
      if bit then
        let added := add other shifted
        ⟨added.data,earlier.allocated+3+added.allocated,
          (bit::rest).length+other.length+shifted.length+3+earlier.held+added.held,
          earlier.work+3+added.work⟩
      else ⟨shifted,earlier.allocated+3,
        (bit::rest).length+other.length+shifted.length+3+earlier.held,earlier.work+3⟩

theorem multiply_data (a b : List Bool) : (multiply a b).data = BinaryMultiplication.multiply a b := by
  induction a with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [multiply,BinaryMultiplication.multiply,
      Bool.false_eq_true,ite_false,ite_true,add_data,ih]

theorem multiply_allocated (a b : List Bool) :
    (multiply a b).allocated = BinaryArithmeticAllocation.multiplyAllocated a b := by
  induction a with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [multiply,BinaryArithmeticAllocation.multiplyAllocated,
      Bool.false_eq_true,ite_false,ite_true,add,addLoop_allocated,multiply_data,ih,Nat.add_zero]

theorem multiply_held (a b : List Bool) :
    (multiply a b).held = BinaryArithmeticAllocation.multiplyHeldPayload a b := by
  induction a with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [multiply,BinaryArithmeticAllocation.multiplyHeldPayload,
      Bool.false_eq_true,ite_false,ite_true,add,addLoop_held,multiply_data,ih,Nat.add_zero]

theorem multiply_erases (a b : List Bool) :
    ((multiply a b).data,(multiply a b).allocated) = BinaryArithmeticAllocation.multiplyWithAllocation a b := by
  rw [BinaryArithmeticAllocation.multiplyWithAllocation_refines,multiply_data,multiply_allocated]

theorem multiply_storage (a b : List Bool) :
    (multiply a b).storage = BinaryArithmeticAllocation.multiplyStorage a b := by
  simp only [Result.storage,multiply_held,multiply_allocated,BinaryArithmeticAllocation.multiplyStorage]

theorem multiply_work (a b : List Bool) : (multiply a b).work = BinaryMultiplication.work a b := by
  induction a with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [multiply,BinaryMultiplication.work,
      Bool.false_eq_true,ite_false,ite_true,add_work,multiply_data,ih,Nat.add_zero]

def borrow : List Bool → List Bool → Bool → List Bool → Result (List Bool × Bool)
  | a::as,b::bs,carry,acc =>
      let later := borrow as bs (BinaryBorrowWord.nextBorrow a b carry)
        (BinaryBorrowWord.difference a b carry::acc)
      ⟨later.data,2+later.allocated,(a::as).length+(b::bs).length+acc.length+2+later.held,later.work+18⟩
  | a,b,carry,acc =>
      let back := reverse acc []
      ⟨(back.1,carry),acc.length,a.length+b.length+acc.length+2,back.2+20⟩

theorem borrow_data (a b : List Bool) (carry : Bool) (acc : List Bool) :
    (borrow a b carry acc).data = BinaryBorrowWord.loop a b carry acc := by
  induction a generalizing b carry acc with
  | nil => cases b <;> simp [borrow,BinaryBorrowWord.loop,reverse_data]
  | cons bit rest ih => cases b with
    | nil => simp [borrow,BinaryBorrowWord.loop,reverse_data]
    | cons other tail => simp only [borrow,BinaryBorrowWord.loop,ih]

theorem borrow_allocated (a b : List Bool) (carry : Bool) (acc : List Bool) :
    (borrow a b carry acc).allocated = BinaryDivisionAllocation.borrowAllocated a b carry acc := by
  induction a generalizing b carry acc with
  | nil => cases b <;> rfl
  | cons bit rest ih => cases b with
    | nil => rfl
    | cons other tail => simp only [borrow,BinaryDivisionAllocation.borrowAllocated,ih]

theorem borrow_held (a b : List Bool) (carry : Bool) (acc : List Bool) :
    (borrow a b carry acc).held = BinaryDivisionAllocation.borrowHeld a b carry acc := by
  induction a generalizing b carry acc with
  | nil => cases b <;> rfl
  | cons bit rest ih => cases b with
    | nil => rfl
    | cons other tail => simp only [borrow,BinaryDivisionAllocation.borrowHeld,ih]

theorem borrow_erases (a b : List Bool) (carry : Bool) (acc : List Bool) :
    ((borrow a b carry acc).data,(borrow a b carry acc).allocated) =
      BinaryDivisionAllocation.borrowWithAllocation a b carry acc := by
  rw [BinaryDivisionAllocation.borrowWithAllocation_refines,borrow_data,borrow_allocated]

theorem borrow_storage (a b : List Bool) :
    (borrow a b false []).storage = BinaryDivisionAllocation.borrowStorage a b := by
  simp only [Result.storage,borrow_held,borrow_allocated,BinaryDivisionAllocation.borrowStorage]

theorem borrow_work (a b : List Bool) (carry : Bool) (acc : List Bool) (h : a.length = b.length) :
    (borrow a b carry acc).work = 22*(a.length+1)+4*acc.length := by
  induction a generalizing b carry acc with
  | nil => cases b with
    | nil => simp only [borrow,reverse_work,List.length_nil]; omega
    | cons other tail => simp at h
  | cons bit rest ih => cases b with
    | nil => simp at h
    | cons other tail =>
        have hh : rest.length = tail.length := by simpa using h
        have hw := ih tail (BinaryBorrowWord.nextBorrow bit other carry)
          (BinaryBorrowWord.difference bit other carry::acc) hh
        simp only [borrow,List.length_cons] at hw ⊢
        omega

end Blotto.BinaryCompareBitsMeasured
