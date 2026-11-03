import Blotto.GeneralPaperTrajectoryAppendStorage

/-! Native local/outer source controllers retain actual counter records,
borrowed source references and recursive frames. Initial/push/branch scratch
uses the retained capacities. No tail-call elimination or physical C-stack
calibration is assumed, and no price accumulator is stored by the source. -/
namespace Blotto.GeneralPaperTrajectoryControllerStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def frame (W capacity count : ℕ) : ℕ := fields W [capacity,count,count+1]+512*W
def frameProfile (W capacity : ℕ) : ℕ := 3*(natBits (capacity+2)+W)+32*W+512*W

theorem frame_bound (W capacity count : ℕ) (hc : count≤capacity) : frame W capacity count≤frameProfile W capacity := by
  have h := fields_bound W (natBits (capacity+2)) [capacity,count,count+1] (by
    intro x hx; apply GeneralPaperRankStorageMonotonicity.nat_word
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    all_goals omega)
  change fields W [capacity,count,count+1]≤3*(natBits (capacity+2)+W)+32*W at h
  exact Nat.add_le_add_right h _

def frameStack (W capacity : ℕ) : ℕ → ℕ
  | 0 => frame W capacity 0
  | count+1 => frameStack W capacity count+frame W capacity (count+1)

theorem stack_bound (W capacity count : ℕ) (hc : count≤capacity) :
    frameStack W capacity count≤(count+1)*frameProfile W capacity := by
  induction count with
  | zero => simpa only [frameStack,Nat.zero_add,Nat.one_mul] using frame_bound W capacity 0 (Nat.zero_le _)
  | succ count ih =>
    have hp := ih (by omega)
    have hn := frame_bound W capacity (count+1) hc
    change frameStack W capacity count+frame W capacity (count+1)≤_
    nlinarith only [hp,hn]

def base (W capacity : ℕ) : ℕ :=
  let A := arrayWord W (capacity+2)
  PaperIndexedArrayConstruction.initialWork (fun w => w) A capacity+
    GeneralPaperIntegerWordPrice.compare (fun w => w) 0 0+64*A

theorem base_bound (W capacity : ℕ) : base W capacity≤256*arrayWord W (capacity+2) :=
  GeneralPaperLocalEpochControlPrice.initial (fun w => w) (fun _ _ h => h) _ capacity
    (GeneralPaperSummaryArrayControls.array_word_positive W (capacity+2)) (GeneralPaperLocalEpochPrice.capacity_word W capacity)

def step (W capacity count : ℕ) : ℕ :=
  let A := arrayWord W (capacity+2)
  PaperIndexedArrayConstruction.stepWork (fun w => w) A count+GeneralPaperLocalEpochExecution.control (fun w => w) A (count+1)

theorem step_bound (W capacity count : ℕ) (hc : count≤capacity) : step W capacity count≤256*arrayWord W (capacity+2) :=
  GeneralPaperLocalEpochControlPrice.step (fun w => w) (fun _ _ h => h) _ capacity count
    (GeneralPaperSummaryArrayControls.array_word_positive W (capacity+2)) hc (GeneralPaperLocalEpochPrice.capacity_word W capacity)

def localWindow (W capacity count : ℕ) : ℕ :=
  frameStack W capacity count+base W capacity+(if count<capacity then step W capacity count else 0)+
    fields W [capacity,count,count+1,capacity+2,0,1]+256*W

def localProfile (W capacity : ℕ) : ℕ :=
  (capacity+1)*frameProfile W capacity+512*arrayWord W (capacity+2)+
    (6*(natBits (capacity+2)+W)+32*W)+256*W

theorem local_bounded (W capacity count : ℕ) (hc : count≤capacity) : localWindow W capacity count≤localProfile W capacity := by
  have hs := (stack_bound W capacity count hc).trans (Nat.mul_le_mul_right (frameProfile W capacity) (Nat.add_le_add_right hc 1))
  have hb := base_bound W capacity
  have hp : (if count<capacity then step W capacity count else 0)≤256*arrayWord W (capacity+2) := by
    split
    · exact step_bound W capacity count hc
    · exact Nat.zero_le _
  have hi := fields_bound W (natBits (capacity+2)) [capacity,count,count+1,capacity+2,0,1] (by
    intro x hx; apply GeneralPaperRankStorageMonotonicity.nat_word
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals omega)
  simp only [List.length_cons,List.length_nil] at hi
  unfold localWindow localProfile
  omega

def outerWindow (W epochs rows count : ℕ) : ℕ :=
  frameStack W epochs count+base W rows+
    GeneralPaperLocalEpochExecution.control (fun w => w) (arrayWord W (epochs+2)) (count+1)+
    fields W [epochs,rows,count,count+1,epochs+2,rows+2]+256*W

def outerProfile (W epochs rows : ℕ) : ℕ :=
  (epochs+1)*frameProfile W epochs+256*arrayWord W (rows+2)+131*arrayWord W (epochs+2)+
    (6*(natBits (epochs+2)+natBits (rows+2)+W)+32*W)+256*W

theorem outer_bounded (W epochs rows count : ℕ) (hc : count≤epochs) : outerWindow W epochs rows count≤outerProfile W epochs rows := by
  have hs := (stack_bound W epochs count hc).trans (Nat.mul_le_mul_right (frameProfile W epochs) (Nat.add_le_add_right hc 1))
  have hb := base_bound W rows
  have hp := GeneralPaperLocalEpochControlPrice.control (fun w => w) (fun _ _ h => h) (arrayWord W (epochs+2)) epochs (count+1) (by omega)
    (GeneralPaperLocalEpochPrice.capacity_word W epochs)
  have hi := fields_bound W (natBits (epochs+2)+natBits (rows+2)) [epochs,rows,count,count+1,epochs+2,rows+2] (by
    intro x hx
    have he := GeneralPaperRankStorageMonotonicity.nat_word epochs (epochs+2) (by omega)
    have hr := GeneralPaperRankStorageMonotonicity.nat_word rows (rows+2) (by omega)
    have hc0 := GeneralPaperRankStorageMonotonicity.nat_word count (epochs+2) (by omega)
    have hc1 := GeneralPaperRankStorageMonotonicity.nat_word (count+1) (epochs+2) (by omega)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals omega)
  simp only [List.length_cons,List.length_nil] at hi
  unfold outerWindow outerProfile
  omega

end Blotto.GeneralPaperTrajectoryControllerStorage
