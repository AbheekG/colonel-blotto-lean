import Blotto.BinaryDivisionAllocation
import Blotto.BinaryWordWidthCore

/-! A Boolean-only borrow guard returns its result and old conservative held/
allocation reservations in the same scan. Cached remaining width and prefix
length replace separate storage/length observers; discarded difference bits
are not constructed. Native scalar arithmetic/representation remains separate.
Metadata identities require the explicit equal-width invariant. -/
namespace Blotto.BinaryBorrowSummaryMeasured
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Result where
  answer : Bool
  work : ℕ
  held : ℕ
  allocated : ℕ

def run : List Bool → List Bool → Bool → ℕ → ℕ → Result
  | a::as,b::bs,carry,remaining,acc =>
      let later := run as bs (BinaryBorrowWord.nextBorrow a b carry) (remaining-1) (acc+1)
      ⟨later.answer,later.work+10,2*remaining+acc+2+later.held,2+later.allocated⟩
  | _,_,carry,_remaining,acc => ⟨carry,10,acc+2,acc⟩

theorem run_answer (a b : List Bool) (carry : Bool) (remaining acc : ℕ) (accBits : List Bool) :
    (run a b carry remaining acc).answer = (BinaryBorrowWord.loop a b carry accBits).2 := by
  induction a generalizing b carry remaining acc accBits with
  | nil => cases b <;> rfl
  | cons bit rest ih => cases b with
    | nil => rfl
    | cons other tail =>
        exact ih tail (BinaryBorrowWord.nextBorrow bit other carry) (remaining-1) (acc+1)
          (BinaryBorrowWord.difference bit other carry::accBits)

theorem run_data (a b : List Bool) (carry : Bool) (remaining acc : ℕ) :
    (run a b carry remaining acc).answer = (BinaryBorrowWord.loop a b carry []).2 :=
  run_answer a b carry remaining acc []

theorem run_work (a b : List Bool) (carry : Bool) (remaining acc : ℕ) :
    (run a b carry remaining acc).work = 10*BinaryBorrowWord.visits a b := by
  induction a generalizing b carry remaining acc with
  | nil => cases b <;> rfl
  | cons bit rest ih => cases b with
    | nil => rfl
    | cons other tail => simp only [run,BinaryBorrowWord.visits,ih]; omega

theorem run_held (a b : List Bool) (carry : Bool) (remaining : ℕ) (acc : List Bool)
    (hA : a.length = remaining) (hB : b.length = remaining) :
    (run a b carry remaining acc.length).held = BinaryDivisionAllocation.borrowHeld a b carry acc := by
  induction a generalizing b carry remaining acc with
  | nil => cases b with
    | nil => simp only [run,BinaryDivisionAllocation.borrowHeld,List.length_nil]; omega
    | cons bit rest => simp only [List.length_nil,List.length_cons] at hA hB; omega
  | cons bit rest ih => cases b with
    | nil => simp only [List.length_nil,List.length_cons] at hA hB; omega
    | cons other tail =>
        have ha : rest.length = remaining-1 := by simp only [List.length_cons] at hA; omega
        have hb : tail.length = remaining-1 := by simp only [List.length_cons] at hB; omega
        have h := ih tail (BinaryBorrowWord.nextBorrow bit other carry) (remaining-1)
          (BinaryBorrowWord.difference bit other carry::acc) ha hb
        simp only [run,BinaryDivisionAllocation.borrowHeld,List.length_cons,hA,hB] at h ⊢
        omega

theorem run_allocated (a b : List Bool) (carry : Bool) (remaining : ℕ) (acc : List Bool)
    (hA : a.length = remaining) (hB : b.length = remaining) :
    (run a b carry remaining acc.length).allocated = BinaryDivisionAllocation.borrowAllocated a b carry acc := by
  induction a generalizing b carry remaining acc with
  | nil => cases b with
    | nil => rfl
    | cons bit rest => simp only [List.length_nil,List.length_cons] at hA hB; omega
  | cons bit rest ih => cases b with
    | nil => simp only [List.length_nil,List.length_cons] at hA hB; omega
    | cons other tail =>
        have ha : rest.length = remaining-1 := by simp only [List.length_cons] at hA; omega
        have hb : tail.length = remaining-1 := by simp only [List.length_cons] at hB; omega
        have h := ih tail (BinaryBorrowWord.nextBorrow bit other carry) (remaining-1)
          (BinaryBorrowWord.difference bit other carry::acc) ha hb
        simpa only [run,BinaryDivisionAllocation.borrowAllocated,List.length_cons] using congrArg (fun n => 2+n) h

theorem run_storage (a b : List Bool) (remaining : ℕ) (hA : a.length = remaining) (hB : b.length = remaining) :
    (run a b false remaining 0).held+(run a b false remaining 0).allocated =
      BinaryDivisionAllocation.borrowStorage a b := by
  have hh := run_held a b false remaining [] hA hB
  have ha := run_allocated a b false remaining [] hA hB
  exact congrArg₂ (fun h a => h+a) hh ha

theorem run_work_bound (a b : List Bool) (width : ℕ) (hA : a.length = width) (hB : b.length = width) :
    (run a b false width 0).work ≤ 22*(width+1) := by
  rw [run_work,BinaryBorrowWord.visits_eq a b (hA.trans hB.symm),hA]
  omega

theorem run_metadata_bound (a b : List Bool) (carry : Bool) (width acc : ℕ)
    (hA : a.length = width) (hB : b.length = width) :
    (run a b carry width acc).held+(run a b carry width acc).allocated ≤ 6*(width+acc+1)^2 := by
  have hh := run_held a b carry width (List.replicate acc false) hA hB
  have hc := run_allocated a b carry width (List.replicate acc false) hA hB
  have hH := BinaryDivisionAllocation.borrowHeld_bound a b carry (List.replicate acc false)
  have hC := BinaryDivisionAllocation.borrowAllocated_bound a b carry (List.replicate acc false)
  simp only [List.length_replicate] at hh hc hH hC
  rw [hA,hB,← hh] at hH
  rw [hA,← hc] at hC
  nlinarith

theorem run_metadata_width (a b : List Bool) (carry : Bool) (width acc : ℕ)
    (hA : a.length = width) (hB : b.length = width) :
    binaryWordWidth ((run a b carry width acc).held+(run a b carry width acc).allocated) ≤
      binaryWordWidth (6*(width+acc+1)^2) :=
  binaryWordWidth_mono (run_metadata_bound a b carry width acc hA hB)

end Blotto.BinaryBorrowSummaryMeasured
