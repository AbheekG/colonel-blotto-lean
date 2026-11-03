import Blotto.BinaryCompareBitsMeasured
import Blotto.BinarySignedAllocation
import Blotto.BinarySignedPaddingMeasured
import Blotto.BinaryBorrowDropMetadata
import Blotto.BinaryAddMultiplyMetadata

/-! Signed arithmetic retains the actual unsigned producer's work/storage
fields. Opposite signs run a backward borrow only on the reached branch. The
old conservative storage for both candidate borrows is derived from the actual
forward borrow's length-invariant observers, without executing a spare borrow.
Padding now executes explicit copy/fill producers and consumes their returned
work in the old reservation. These are source reservations; native metadata,
instruction/ownership/GC interpretation remains open. -/
namespace Blotto.BinaryCompareSignedMeasured
open BinarySignedMagnitude
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Result where
  data : Word
  allocated : ℕ
  storage : ℕ
  work : ℕ

theorem borrow_observers_swap (a b : List Bool) (carry other : Bool)
    (acc extra : List Bool) (h : a.length = b.length) (hAcc : acc.length = extra.length) :
    BinaryDivisionAllocation.borrowAllocated a b carry acc =
      BinaryDivisionAllocation.borrowAllocated b a other extra ∧
    BinaryDivisionAllocation.borrowHeld a b carry acc =
      BinaryDivisionAllocation.borrowHeld b a other extra := by
  induction a generalizing b carry other acc extra with
  | nil => cases b with
    | nil => simp only [BinaryDivisionAllocation.borrowAllocated,BinaryDivisionAllocation.borrowHeld,List.length_nil]; omega
    | cons bit rest => simp at h
  | cons bit rest ih => cases b with
    | nil => simp at h
    | cons next tail =>
        have hTail : rest.length = tail.length := by simpa using h
        have hAcc' : (BinaryBorrowWord.difference bit next carry::acc).length =
            (BinaryBorrowWord.difference next bit other::extra).length := by simpa using hAcc
        obtain ⟨ha,hh⟩ := ih tail (BinaryBorrowWord.nextBorrow bit next carry)
          (BinaryBorrowWord.nextBorrow next bit other)
          (BinaryBorrowWord.difference bit next carry::acc)
          (BinaryBorrowWord.difference next bit other::extra) hTail hAcc'
        simp only [BinaryDivisionAllocation.borrowAllocated,BinaryDivisionAllocation.borrowHeld,
          List.length_cons] at ha hh ⊢
        constructor <;> omega

theorem borrowStorage_swap (a b : List Bool) (h : a.length = b.length) :
    BinaryDivisionAllocation.borrowStorage a b = BinaryDivisionAllocation.borrowStorage b a := by
  obtain ⟨ha,hh⟩ := borrow_observers_swap a b false false [] [] h rfl
  unfold BinaryDivisionAllocation.borrowStorage
  omega

def differenceAt (first second : List Bool) (n m : ℕ) : Result × ℕ :=
  let W := max n m
  let a := BinarySignedPaddingMeasured.pad W first
  let b := BinarySignedPaddingMeasured.pad W second
  let forward := BinaryBorrowDropMetadata.borrowAt a.1.1 b.1.1 false [] W W 0
  if forward.data.2 then
    let backward := BinaryBorrowDropMetadata.borrowAt b.1.1 a.1.1 false [] W W 0
    let allocated := a.1.2+b.1.2+forward.allocated+backward.allocated+4
    (⟨⟨true,backward.data.1⟩,allocated,
      n+m+4*W+6+2*forward.storage+allocated,
      a.2+b.2+forward.work+backward.work⟩,W)
  else
    let allocated := a.1.2+b.1.2+forward.allocated+4
    (⟨⟨false,forward.data.1⟩,allocated,
      n+m+4*W+6+2*forward.storage+allocated,
      a.2+b.2+forward.work⟩,W)

theorem differenceAt_record (first second : List Bool) (n m : ℕ)
    (hN : n=first.length) (hM : m=second.length) :
    (differenceAt first second n m).1 = (
  let W := max first.length second.length
  let a := BinarySignedPaddingMeasured.pad W first
  let b := BinarySignedPaddingMeasured.pad W second
  let forward := BinaryBorrowDropMetadata.borrowAt a.1.1 b.1.1 false [] W W 0
  if forward.data.2 then
    let backward := BinaryBorrowDropMetadata.borrowAt b.1.1 a.1.1 false [] W W 0
    let allocated := a.1.2+b.1.2+forward.allocated+backward.allocated+4
    ⟨⟨true,backward.data.1⟩,allocated,
      first.length+second.length+4*W+6+2*forward.storage+allocated,
      a.2+b.2+forward.work+backward.work⟩
  else
    let allocated := a.1.2+b.1.2+forward.allocated+4
    ⟨⟨false,forward.data.1⟩,allocated,
      first.length+second.length+4*W+6+2*forward.storage+allocated,
      a.2+b.2+forward.work⟩) := by
  subst n; subst m
  simp only [differenceAt]
  split <;> rfl

def differenceProduced (first second : List Bool) : (Result × ℕ) × (ℕ × ℕ) :=
  let n := BinaryBorrowDropMetadata.countFrom first 0
  let m := BinaryBorrowDropMetadata.countFrom second 0
  (differenceAt first second n m,(n,m))

theorem differenceProduced_record (first second : List Bool) :
    (differenceProduced first second).1.1 = (
  let W := max first.length second.length
  let a := BinarySignedPaddingMeasured.pad W first
  let b := BinarySignedPaddingMeasured.pad W second
  let forward := BinaryBorrowDropMetadata.borrowAt a.1.1 b.1.1 false [] W W 0
  if forward.data.2 then
    let backward := BinaryBorrowDropMetadata.borrowAt b.1.1 a.1.1 false [] W W 0
    let allocated := a.1.2+b.1.2+forward.allocated+backward.allocated+4
    ⟨⟨true,backward.data.1⟩,allocated,
      first.length+second.length+4*W+6+2*forward.storage+allocated,
      a.2+b.2+forward.work+backward.work⟩
  else
    let allocated := a.1.2+b.1.2+forward.allocated+4
    ⟨⟨false,forward.data.1⟩,allocated,
      first.length+second.length+4*W+6+2*forward.storage+allocated,
      a.2+b.2+forward.work⟩) := by
  apply differenceAt_record
  · simp [BinaryBorrowDropMetadata.count_exact]
  · simp [BinaryBorrowDropMetadata.count_exact]

def difference (first second : List Bool) : Result := (differenceProduced first second).1.1

theorem difference_previous_record (first second : List Bool) :
    difference first second = (
  let W := max first.length second.length
  let a := BinarySignedPaddingMeasured.pad W first
  let b := BinarySignedPaddingMeasured.pad W second
  let forward := BinaryBorrowDropMetadata.borrowAt a.1.1 b.1.1 false [] W W 0
  if forward.data.2 then
    let backward := BinaryBorrowDropMetadata.borrowAt b.1.1 a.1.1 false [] W W 0
    let allocated := a.1.2+b.1.2+forward.allocated+backward.allocated+4
    ⟨⟨true,backward.data.1⟩,allocated,
      first.length+second.length+4*W+6+2*forward.storage+allocated,
      a.2+b.2+forward.work+backward.work⟩
  else
    let allocated := a.1.2+b.1.2+forward.allocated+4
    ⟨⟨false,forward.data.1⟩,allocated,
      first.length+second.length+4*W+6+2*forward.storage+allocated,
      a.2+b.2+forward.work⟩) := differenceProduced_record first second

theorem difference_record (first second : List Bool) :
    difference first second =
    let W := max first.length second.length
    let a := BinarySignedAllocation.padWithAllocation W first
    let b := BinarySignedAllocation.padWithAllocation W second
    let forward := BinaryCompareBitsMeasured.borrow a.1 b.1 false []
    if forward.data.2 then
      let backward := BinaryCompareBitsMeasured.borrow b.1 a.1 false []
      let allocated := a.2+b.2+forward.allocated+backward.allocated+4
      ⟨⟨true,backward.data.1⟩,allocated,
        first.length+second.length+4*W+6+2*forward.storage+allocated,
        4*(W+1)+forward.work+backward.work⟩
    else
      let allocated := a.2+b.2+forward.allocated+4
      ⟨⟨false,forward.data.1⟩,allocated,
        first.length+second.length+4*W+6+2*forward.storage+allocated,
        4*(W+1)+forward.work⟩
  := by
  let W := max first.length second.length
  have ha := BinarySignedPaddingMeasured.pad_width W first (Nat.le_max_left _ _)
  have hb := BinarySignedPaddingMeasured.pad_width W second (Nat.le_max_right _ _)
  have hw : 2*(W+1)+2*(W+1) = 4*(W+1) := by omega
  have haLen : W=(BinarySignedPaddingMeasured.pad W first).1.1.length := by
    rw [BinarySignedPaddingMeasured.pad_compat]
    exact (pad_length W first (Nat.le_max_left _ _)).symm
  have hbLen : W=(BinarySignedPaddingMeasured.pad W second).1.1.length := by
    rw [BinarySignedPaddingMeasured.pad_compat]
    exact (pad_length W second (Nat.le_max_right _ _)).symm
  have hf := BinaryBorrowDropMetadata.borrow_exact
    (BinarySignedPaddingMeasured.pad W first).1.1 (BinarySignedPaddingMeasured.pad W second).1.1
    false [] W W 0 haLen hbLen rfl
  have hr := BinaryBorrowDropMetadata.borrow_exact
    (BinarySignedPaddingMeasured.pad W second).1.1 (BinarySignedPaddingMeasured.pad W first).1.1
    false [] W W 0 hbLen haLen rfl
  simp only [BinarySignedPaddingMeasured.pad_compat] at hf hr
  dsimp only [W] at ha hb hw hf hr
  simp only [difference_previous_record,BinarySignedPaddingMeasured.pad_compat,ha,hb,hw,hf,hr]

theorem difference_padding_work (first second : List Bool) :
    let W := max first.length second.length
    (BinarySignedPaddingMeasured.pad W first).2+
      (BinarySignedPaddingMeasured.pad W second).2 ≤ (difference first second).work := by
  have ha := BinarySignedPaddingMeasured.pad_width (max first.length second.length) first (Nat.le_max_left _ _)
  have hb := BinarySignedPaddingMeasured.pad_width (max first.length second.length) second (Nat.le_max_right _ _)
  rw [difference_record]
  simp only [ha,hb]
  split <;> dsimp only <;> omega

theorem difference_padding_allocated (first second : List Bool) :
    let W := max first.length second.length
    (BinarySignedPaddingMeasured.pad W first).1.2+
      (BinarySignedPaddingMeasured.pad W second).1.2 ≤ (difference first second).allocated := by
  rw [difference_record]
  simp only [BinarySignedPaddingMeasured.pad_compat]
  split <;> dsimp only <;> omega

theorem difference_erases (first second : List Bool) :
    ((difference first second).data,(difference first second).allocated) =
      BinarySignedAllocation.differenceWithAllocation first second := by
  simp only [difference_record,BinarySignedAllocation.differenceWithAllocation,
    ← BinaryCompareBitsMeasured.borrow_erases]
  split <;> rfl

theorem difference_data (first second : List Bool) :
    (difference first second).data = BinarySignedMagnitude.difference first second := by
  exact (congrArg Prod.fst (difference_erases first second)).trans
    (BinarySignedAllocation.differenceWithAllocation_state first second)

theorem difference_allocated (first second : List Bool) :
    (difference first second).allocated = (BinarySignedAllocation.differenceWithAllocation first second).2 :=
  congrArg Prod.snd (difference_erases first second)

theorem difference_storage (first second : List Bool) :
    (difference first second).storage = BinarySignedAllocation.differenceStorage first second := by
  let W := max first.length second.length
  let a := pad W first
  let b := pad W second
  have ha : a.length = W := pad_length W first (Nat.le_max_left _ _)
  have hb : b.length = W := pad_length W second (Nat.le_max_right _ _)
  have hBoth := ha.trans hb.symm
  have hf := BinaryBorrowWord.subtract_length a b false hBoth
  have hr := BinaryBorrowWord.subtract_length b a false hBoth.symm
  have hStorage := borrowStorage_swap a b hBoth
  have hAlloc := difference_allocated first second
  unfold BinarySignedAllocation.differenceStorage
  change _ = first.length+second.length+a.length+b.length+
    (BinaryBorrowWord.subtract a b false).1.length+
    (BinaryBorrowWord.subtract b a false).1.length+6+
    BinaryDivisionAllocation.borrowStorage a b+BinaryDivisionAllocation.borrowStorage b a+
    (BinarySignedAllocation.differenceWithAllocation first second).2
  rw [hf,hr,ha,hb,← hStorage,← hAlloc]
  rw [difference_record]
  dsimp only
  split <;> simp only [BinarySignedAllocation.padWithAllocation,
    BinaryCompareBitsMeasured.borrow_storage]
  all_goals dsimp only [a,b,W] at *; omega

theorem difference_work (first second : List Bool) :
    (difference first second).work = BinarySignedMagnitude.differenceWork first second := by
  let W := max first.length second.length
  have ha := pad_length W first (Nat.le_max_left _ _)
  have hb := pad_length W second (Nat.le_max_right _ _)
  have hf := BinaryCompareBitsMeasured.borrow_work (pad W first) (pad W second) false [] (ha.trans hb.symm)
  have hr := BinaryCompareBitsMeasured.borrow_work (pad W second) (pad W first) false [] (hb.trans ha.symm)
  rw [ha,List.length_nil,mul_zero,Nat.add_zero] at hf
  rw [hb,List.length_nil,mul_zero,Nat.add_zero] at hr
  dsimp only [W] at hf hr
  simp only [difference_record,BinarySignedMagnitude.differenceWork,
    BinarySignedAllocation.padWithAllocation,hf,hr,
    BinaryCompareBitsMeasured.borrow_data,BinaryBorrowWord.subtract]
  split <;> rename_i h <;> simp only [h,Bool.false_eq_true,ite_true,ite_false,Nat.add_zero]


theorem differenceProduced_public (first second : List Bool) :
    (differenceProduced first second).1.1 = difference first second := rfl

theorem differenceAt_public (first second : List Bool) (n m : ℕ)
    (hN : n=first.length) (hM : m=second.length) :
    (differenceAt first second n m).1 = difference first second := by
  rw [difference_previous_record]
  exact differenceAt_record first second n m hN hM

theorem differenceAt_width (first second : List Bool) (n m : ℕ)
    (hN : n=first.length) (hM : m=second.length) :
    (differenceAt first second n m).2 = (differenceAt first second n m).1.data.bits.length := by
  have hw : (differenceAt first second n m).2 = max n m := by
    simp only [differenceAt]
    split <;> rfl
  rw [hw,differenceAt_public first second n m hN hM,difference_data,
    BinarySignedMagnitude.difference_length,hN,hM]

theorem differenceProduced_lengths (first second : List Bool) :
    (differenceProduced first second).2 = (first.length,second.length) := by
  simp only [differenceProduced,BinaryBorrowDropMetadata.count_exact,Nat.zero_add]

theorem differenceProduced_width (first second : List Bool) :
    (differenceProduced first second).1.2 = (differenceProduced first second).1.1.data.bits.length := by
  apply differenceAt_width
  · simp [BinaryBorrowDropMetadata.count_exact]
  · simp [BinaryBorrowDropMetadata.count_exact]

theorem difference_setup_work_bound (first second : List Bool) :
    (differenceProduced first second).2.1+(differenceProduced first second).2.2+2 ≤
      (differenceProduced first second).1.1.work := by
  have h := difference_padding_work first second
  have ha := BinarySignedPaddingMeasured.pad_width (max first.length second.length) first (Nat.le_max_left _ _)
  have hb := BinarySignedPaddingMeasured.pad_width (max first.length second.length) second (Nat.le_max_right _ _)
  simp only [differenceProduced_lengths,differenceProduced_public,ha,hb] at h ⊢
  omega

def addProduced (first second : Word) : (Result × ℕ) × (ℕ × ℕ) :=
  if first.negative = second.negative then
    let produced := BinaryAddMultiplyMetadata.addProduced first.bits second.bits
    let added := produced.1.1
    ((⟨⟨first.negative,added.data⟩,added.allocated+3,
      produced.2.1+produced.2.2+4+added.storage,3+added.work⟩,produced.1.2),produced.2)
  else if first.negative then
    let produced := differenceProduced second.bits first.bits
    let result := produced.1.1
    ((⟨result.data,result.allocated+3,produced.2.1+produced.2.2+4+result.storage,3+result.work⟩,
      produced.1.2),(produced.2.2,produced.2.1))
  else
    let produced := differenceProduced first.bits second.bits
    let result := produced.1.1
    ((⟨result.data,result.allocated+3,produced.2.1+produced.2.2+4+result.storage,3+result.work⟩,
      produced.1.2),produced.2)

theorem addProduced_record (first second : Word) :
    (addProduced first second).1.1 = (
  if first.negative = second.negative then
    let produced := BinaryAddMultiplyMetadata.addProduced first.bits second.bits
    let added := produced.1.1
    ⟨⟨first.negative,added.data⟩,added.allocated+3,
      produced.2.1+produced.2.2+4+added.storage,3+added.work⟩
  else if first.negative then
    let result := difference second.bits first.bits
    ⟨result.data,result.allocated+3,first.bits.length+second.bits.length+4+result.storage,3+result.work⟩
  else
    let result := difference first.bits second.bits
    ⟨result.data,result.allocated+3,first.bits.length+second.bits.length+4+result.storage,3+result.work⟩) := by
  simp only [addProduced,BinaryAddMultiplyMetadata.addProduced_lengths,
    differenceProduced_lengths,differenceProduced_public]
  split
  · rfl
  · split
    · simp only [Nat.add_comm second.bits.length first.bits.length]
    · rfl

theorem addProduced_lengths (first second : Word) :
    (addProduced first second).2 = (first.bits.length,second.bits.length) := by
  simp only [addProduced,BinaryAddMultiplyMetadata.addProduced_lengths,differenceProduced_lengths]
  split
  · rfl
  · split <;> rfl

theorem addProduced_width (first second : Word) :
    (addProduced first second).1.2 = (addProduced first second).1.1.data.bits.length := by
  simp only [addProduced]
  split
  · exact BinaryAddMultiplyMetadata.addProduced_width first.bits second.bits
  · split <;> exact differenceProduced_width _ _

def add (first second : Word) : Result := (addProduced first second).1.1

theorem addProduced_public (first second : Word) :
    (addProduced first second).1.1 = add first second := rfl

theorem add_previous_record (first second : Word) :
    add first second = (
  if first.negative = second.negative then
    let added := BinaryCompareBitsMeasured.add first.bits second.bits
    ⟨⟨first.negative,added.data⟩,added.allocated+3,
      first.bits.length+second.bits.length+4+added.storage,3+added.work⟩
  else if first.negative then
    let result := difference second.bits first.bits
    ⟨result.data,result.allocated+3,first.bits.length+second.bits.length+4+result.storage,3+result.work⟩
  else
    let result := difference first.bits second.bits
    ⟨result.data,result.allocated+3,first.bits.length+second.bits.length+4+result.storage,3+result.work⟩) := by
  simp only [add,addProduced_record,BinaryAddMultiplyMetadata.addProduced_lengths,BinaryAddMultiplyMetadata.addProduced_record]

theorem add_erases (first second : Word) :
    ((add first second).data,(add first second).allocated) = BinarySignedAllocation.addWithAllocation first second := by
  simp only [add_previous_record,BinarySignedAllocation.addWithAllocation,
    ← BinaryCompareBitsMeasured.add_erases,← difference_erases]
  split
  · rfl
  · split <;> rfl

theorem add_data (first second : Word) : (add first second).data = BinarySignedMagnitude.add first second := by
  exact (congrArg Prod.fst (add_erases first second)).trans (BinarySignedAllocation.addWithAllocation_state first second)

theorem add_storage (first second : Word) : (add first second).storage = BinarySignedAllocation.addStorage first second := by
  simp only [add_previous_record,BinarySignedAllocation.addStorage,BinaryCompareBitsMeasured.add_storage,difference_storage]
  split
  · rfl
  · split <;> rfl

theorem add_work (first second : Word) : (add first second).work = BinarySignedMagnitude.addWork first second := by
  simp only [add_previous_record,BinarySignedMagnitude.addWork,BinaryCompareBitsMeasured.add_work,difference_work]
  split
  · rfl
  · split <;> rfl

def subtractProduced (first second : Word) : (Result × ℕ) × (ℕ × ℕ) :=
  let produced := addProduced first (BinarySignedMagnitude.negate second)
  let result := produced.1.1
  ((⟨result.data,result.allocated+1,result.storage,result.work⟩,produced.1.2),produced.2)

theorem subtractProduced_record (first second : Word) :
    (subtractProduced first second).1.1 = (
  let result := add first (BinarySignedMagnitude.negate second)
  ⟨result.data,result.allocated+1,result.storage,result.work⟩) := by rfl

theorem subtractProduced_lengths (first second : Word) :
    (subtractProduced first second).2 = (first.bits.length,second.bits.length) := by
  simp only [subtractProduced,addProduced_lengths,BinarySignedMagnitude.negate]

theorem subtractProduced_width (first second : Word) :
    (subtractProduced first second).1.2 = (subtractProduced first second).1.1.data.bits.length :=
  addProduced_width first (BinarySignedMagnitude.negate second)

def subtract (first second : Word) : Result := (subtractProduced first second).1.1

theorem subtract_previous_record (first second : Word) :
    subtract first second = (
  let result := add first (BinarySignedMagnitude.negate second)
  ⟨result.data,result.allocated+1,result.storage,result.work⟩) := subtractProduced_record first second

theorem subtractProduced_public (first second : Word) :
    (subtractProduced first second).1.1 = subtract first second := rfl

theorem subtract_erases (first second : Word) :
    ((subtract first second).data,(subtract first second).allocated) = BinarySignedAllocation.subtractWithAllocation first second := by
  simp only [subtract_previous_record,BinarySignedAllocation.subtractWithAllocation,← add_erases]

theorem subtract_data (first second : Word) :
    (subtract first second).data = BinarySignedMagnitude.subtract first second := add_data _ _

theorem subtract_storage (first second : Word) :
    (subtract first second).storage = BinarySignedAllocation.addStorage first (BinarySignedMagnitude.negate second) := add_storage _ _

theorem subtract_work (first second : Word) :
    (subtract first second).work = BinarySignedMagnitude.addWork first (BinarySignedMagnitude.negate second) := add_work _ _

def multiplyProduced (first second : Word) : (Result × ℕ) × (ℕ × ℕ) :=
  let produced := BinaryAddMultiplyMetadata.multiplyProduced first.bits second.bits
  let result := produced.1.1
  ((⟨⟨Bool.xor first.negative second.negative,result.data⟩,result.allocated+2,
    produced.2.1+produced.2.2+3+result.storage,1+result.work⟩,produced.1.2),produced.2)

theorem multiplyProduced_record (first second : Word) :
    (multiplyProduced first second).1.1 = (
  let produced := BinaryAddMultiplyMetadata.multiplyProduced first.bits second.bits
  let result := produced.1.1
  ⟨⟨Bool.xor first.negative second.negative,result.data⟩,result.allocated+2,
    produced.2.1+produced.2.2+3+result.storage,1+result.work⟩) := by rfl

theorem multiplyProduced_lengths (first second : Word) :
    (multiplyProduced first second).2 = (first.bits.length,second.bits.length) := by
  simp only [multiplyProduced,BinaryAddMultiplyMetadata.multiplyProduced_lengths]

theorem multiplyProduced_width (first second : Word) :
    (multiplyProduced first second).1.2 = (multiplyProduced first second).1.1.data.bits.length :=
  BinaryAddMultiplyMetadata.multiplyProduced_width first.bits second.bits

def multiply (first second : Word) : Result := (multiplyProduced first second).1.1

attribute [irreducible] differenceAt differenceProduced addProduced subtractProduced multiplyProduced

theorem multiplyProduced_public (first second : Word) :
    (multiplyProduced first second).1.1 = multiply first second := rfl

theorem multiply_previous_record (first second : Word) :
    multiply first second = (
  let result := BinaryCompareBitsMeasured.multiply first.bits second.bits
  ⟨⟨Bool.xor first.negative second.negative,result.data⟩,result.allocated+2,
    first.bits.length+second.bits.length+3+result.storage,1+result.work⟩) := by
  simp only [multiply,multiplyProduced_record,BinaryAddMultiplyMetadata.multiplyProduced_lengths,BinaryAddMultiplyMetadata.multiplyProduced_record]

theorem multiply_erases (first second : Word) :
    ((multiply first second).data,(multiply first second).allocated) = BinarySignedAllocation.multiplyWithAllocation first second := by
  simp only [multiply_previous_record,BinarySignedAllocation.multiplyWithAllocation,← BinaryCompareBitsMeasured.multiply_erases]

theorem multiply_data (first second : Word) : (multiply first second).data = BinarySignedMagnitude.multiply first second := by
  exact (congrArg Prod.fst (multiply_erases first second)).trans (BinarySignedAllocation.multiplyWithAllocation_state first second)

theorem multiply_storage (first second : Word) : (multiply first second).storage = BinarySignedAllocation.multiplyStorage first second := by
  simp only [multiply_previous_record,BinarySignedAllocation.multiplyStorage,BinaryCompareBitsMeasured.multiply_storage]

theorem multiply_work (first second : Word) : (multiply first second).work = BinarySignedMagnitude.multiplyWork first second := by
  simp only [multiply_previous_record,BinarySignedMagnitude.multiplyWork,BinaryCompareBitsMeasured.multiply_work]


end Blotto.BinaryCompareSignedMeasured
