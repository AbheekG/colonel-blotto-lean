import Blotto.BinaryCompareBitsMeasured

/-! Cached widths follow actual borrow/drop recursion. No per-case list-length
observer constructs allocation or held metadata. Tail loops count input widths
and reverse actual buffers. Complete old fields remain exact for valid caches;
caller proofs derive those caches without adding a public model premise.
Native counter arithmetic/reference/record/ownership/GC joins remain open. -/
namespace Blotto.BinaryBorrowDropMetadata
open BinaryCompareBitsMeasured (Result)
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem record_ext {α : Type} {first second : Result α}
    (hData : first.data=second.data) (hAllocated : first.allocated=second.allocated)
    (hHeld : first.held=second.held) (hWork : first.work=second.work) : first=second := by
  cases first; cases second
  cases hData; cases hAllocated; cases hHeld; cases hWork
  rfl

def countFrom : List Bool → ℕ → ℕ
  | [],count => count
  | _::rest,count => countFrom rest (count+1)

theorem count_exact (bits : List Bool) (count : ℕ) : countFrom bits count = count+bits.length := by
  induction bits generalizing count with
  | nil => rfl
  | cons bit rest ih => simp only [countFrom,ih,List.length_cons]; omega

def reverseFrom : List Bool → List Bool → ℕ → List Bool × ℕ
  | [],acc,work => (acc,work)
  | bit::rest,acc,work => reverseFrom rest (bit::acc) (work+4)

theorem reverse_data (bits acc : List Bool) (work : ℕ) :
    (reverseFrom bits acc work).1 = bits.reverse++acc := by
  induction bits generalizing acc work with
  | nil => rfl
  | cons bit rest ih => simp [reverseFrom,ih,List.reverse_cons,List.append_assoc]

theorem reverse_work (bits acc : List Bool) (work : ℕ) :
    (reverseFrom bits acc work).2 = work+4*bits.length := by
  induction bits generalizing acc work with
  | nil => rfl
  | cons bit rest ih => simp only [reverseFrom,ih,List.length_cons]; omega

theorem reverse_exact (bits acc : List Bool) :
    reverseFrom bits acc 2 = BinaryCompareBitsMeasured.reverse bits acc := by
  apply Prod.ext
  · simp only [reverse_data,BinaryCompareBitsMeasured.reverse_data]
  · simp only [reverse_work,BinaryCompareBitsMeasured.reverse_work]; omega

def appendFalse : List Bool → (List Bool × ℕ) × ℕ
  | [] => (([false],0),4)
  | bit::rest =>
      let later := appendFalse rest
      ((bit::later.1.1,later.1.2+1),later.2+4)

theorem appendFalse_record (bits : List Bool) :
    appendFalse bits = ((bits++[false],bits.length),4*(bits.length+1)) := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      simp only [appendFalse,ih,List.cons_append,List.length_cons]
      congr 2

def borrowAt : List Bool → List Bool → Bool → List Bool → ℕ → ℕ → ℕ → Result (List Bool × Bool)
  | a::as,b::bs,carry,acc,n,m,k =>
      let later := borrowAt as bs (BinaryBorrowWord.nextBorrow a b carry)
        (BinaryBorrowWord.difference a b carry::acc) (n-1) (m-1) (k+1)
      ⟨later.data,2+later.allocated,n+m+k+2+later.held,later.work+18⟩
  | _,_,carry,acc,n,m,k =>
      let back := reverseFrom acc [] 2
      ⟨(back.1,carry),k,n+m+k+2,back.2+20⟩

theorem borrow_exact (a b : List Bool) (carry : Bool) (acc : List Bool) (n m k : ℕ)
    (hA : n=a.length) (hB : m=b.length) (hK : k=acc.length) :
    borrowAt a b carry acc n m k = BinaryCompareBitsMeasured.borrow a b carry acc := by
  subst n; subst m; subst k
  induction a generalizing b carry acc with
  | nil => cases b <;> simp only [borrowAt,BinaryCompareBitsMeasured.borrow,reverse_exact]
  | cons bit rest ih => cases b with
    | nil => simp only [borrowAt,BinaryCompareBitsMeasured.borrow,reverse_exact]
    | cons other tail =>
        have h := ih tail (BinaryBorrowWord.nextBorrow bit other carry)
          (BinaryBorrowWord.difference bit other carry::acc)
        simp only [List.length_cons] at h
        simp only [borrowAt,BinaryCompareBitsMeasured.borrow,List.length_cons,Nat.add_sub_cancel,h]

theorem borrow_loop_length (a b : List Bool) (carry : Bool) (acc : List Bool) :
    (BinaryBorrowWord.loop a b carry acc).1.length = min a.length b.length+acc.length := by
  induction a generalizing b carry acc with
  | nil => cases b <;> simp [BinaryBorrowWord.loop]
  | cons bit rest ih => cases b with
    | nil => simp [BinaryBorrowWord.loop]
    | cons other tail => simp only [BinaryBorrowWord.loop,ih,List.length_cons]; omega

theorem borrow_length (a b : List Bool) (carry : Bool) (acc : List Bool) (n m k : ℕ)
    (hA : n=a.length) (hB : m=b.length) (hK : k=acc.length) :
    (borrowAt a b carry acc n m k).data.1.length = min n m+k := by
  rw [borrow_exact a b carry acc n m k hA hB hK,BinaryCompareBitsMeasured.borrow_data,borrow_loop_length]
  rw [hA,hB,hK]

theorem borrow_reference_work (a b : List Bool) (carry : Bool) (acc : List Bool) :
    (BinaryCompareBitsMeasured.borrow a b carry acc).work = 22*(min a.length b.length+1)+4*acc.length := by
  induction a generalizing b carry acc with
  | nil => cases b <;> simp only [BinaryCompareBitsMeasured.borrow,BinaryCompareBitsMeasured.reverse_work,List.length_nil,Nat.zero_min,Nat.min_zero,Nat.zero_add,Nat.mul_one] <;> omega
  | cons bit rest ih => cases b with
    | nil => simp only [BinaryCompareBitsMeasured.borrow,BinaryCompareBitsMeasured.reverse_work,List.length_nil,Nat.zero_min,Nat.min_zero,Nat.zero_add,Nat.mul_one] <;> omega
    | cons other tail => simp only [BinaryCompareBitsMeasured.borrow,ih,List.length_cons]; omega

theorem borrow_work (a b : List Bool) (carry : Bool) (acc : List Bool) (n m k : ℕ)
    (hA : n=a.length) (hB : m=b.length) (hK : k=acc.length) :
    (borrowAt a b carry acc n m k).work = 22*(min n m+1)+4*k := by
  rw [borrow_exact a b carry acc n m k hA hB hK,borrow_reference_work,hA,hB,hK]

theorem dropHeld_acc_length (bits first second : List Bool) (h : first.length=second.length) :
    BinaryDivisionAllocation.dropHeld bits first = BinaryDivisionAllocation.dropHeld bits second := by
  induction bits generalizing first second with
  | nil => simpa only [BinaryDivisionAllocation.dropHeld] using congrArg (fun n => n+1) h
  | cons bit rest ih => cases rest with
    | nil => simp only [BinaryDivisionAllocation.dropHeld,h]
    | cons next tail =>
        simp only [BinaryDivisionAllocation.dropHeld,h]
        rw [ih (false::first) (false::second) (by simpa using h)]

def dropAt : List Bool → List Bool → ℕ → ℕ → Result (List Bool)
  | [],acc,_,k =>
      let back := reverseFrom acc [] 2
      ⟨back.1,k,k+1,back.2+2⟩
  | [_],acc,_,k =>
      let back := reverseFrom acc [] 2
      ⟨back.1,k,1+k+1,back.2+2⟩
  | bit::next::rest,acc,n,k =>
      let later := dropAt (next::rest) (bit::acc) (n-1) (k+1)
      ⟨later.data,2+later.allocated,n+k+1+later.held,later.work+4⟩

theorem drop_data (bits acc : List Bool) (n k : ℕ) :
    (dropAt bits acc n k).data = BinaryWordHighBit.loop bits acc := by
  induction bits generalizing acc n k with
  | nil => simp [dropAt,BinaryWordHighBit.loop,reverse_data]
  | cons bit rest ih => cases rest with
    | nil => simp [dropAt,BinaryWordHighBit.loop,reverse_data]
    | cons next tail => simp only [dropAt,BinaryWordHighBit.loop,ih]

theorem drop_allocated (bits acc : List Bool) (n k : ℕ) (hK : k=acc.length) :
    (dropAt bits acc n k).allocated = BinaryDivisionAllocation.dropAllocated bits acc := by
  subst k
  induction bits generalizing acc n with
  | nil => rfl
  | cons bit rest ih => cases rest with
    | nil => rfl
    | cons next tail =>
        have h := ih (bit::acc) (n-1)
        simp only [List.length_cons] at h
        simp only [dropAt,BinaryDivisionAllocation.dropAllocated,h]
        rw [BinaryDivisionAllocation.dropAllocated_acc_length (next::tail) (bit::acc) (false::acc) rfl]

theorem drop_held (bits acc : List Bool) (n k : ℕ) (hN : n=bits.length) (hK : k=acc.length) :
    (dropAt bits acc n k).held = BinaryDivisionAllocation.dropHeld bits acc := by
  subst n; subst k
  induction bits generalizing acc with
  | nil => rfl
  | cons bit rest ih => cases rest with
    | nil => rfl
    | cons next tail =>
        have h := ih (bit::acc)
        simp only [List.length_cons] at h
        simp only [dropAt,BinaryDivisionAllocation.dropHeld,List.length_cons,Nat.add_sub_cancel,h]
        rw [dropHeld_acc_length (next::tail) (bit::acc) (false::acc) rfl]

theorem drop_work (bits acc : List Bool) (n k : ℕ) :
    (dropAt bits acc n k).work = 8*(bits.length-1)+4*acc.length+4 := by
  induction bits generalizing acc n k with
  | nil => simp only [dropAt,reverse_work,List.length_nil,List.length_cons,Nat.zero_sub,Nat.mul_zero] <;> omega
  | cons bit rest ih => cases rest with
    | nil => simp only [dropAt,reverse_work,List.length_nil,List.length_cons,Nat.zero_sub,Nat.mul_zero] <;> omega
    | cons next tail =>
        have h := ih (bit::acc) (n-1) (k+1)
        simp only [dropAt,List.length_cons] at h ⊢
        omega

end Blotto.BinaryBorrowDropMetadata
