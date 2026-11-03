import Blotto.GeneralPaperScoreDPHeight
import Blotto.PaperIndexedArrayConstruction

/-! Declared unit-operation profile of the actual stored score DP. A
candidate pays two indexed reads, a score guard/subtraction, at most one
rational addition and fixed witness/option fields (16 units). A minimum
pays at most one rational comparison and fixed fields (8 units); each scan
step pays four control units. Array construction uses the retained priced
indexed loop. These are source-model operations, not a native library rate.
Rational bit costs, score-matrix preparation, the final threshold scan and
simultaneous storage must still be joined in the general-paper cost proof.
-/
namespace Blotto.GeneralPaperScoreDPWork
open GeneralPaperMinimum GeneralPaperExactScoreDP
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000

def scanRun {α : Type*} {K : ℕ} (evaluate : α → Option (Selection K) × ℕ) :
    List α → Option (Selection K) × ℕ
  | [] => (none,2)
  | a::rest =>
      let current := evaluate a
      let later := scanRun evaluate rest
      (pick current.1 later.1,current.2+later.2+8+4)

theorem scan_data {α : Type*} {K : ℕ} (evaluate : α → Option (Selection K) × ℕ) (xs : List α) :
    (scanRun evaluate xs).1=scan (fun a => (evaluate a).1) xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp only [scanRun,scan,ih]

theorem scan_work {α : Type*} {K : ℕ} (evaluate : α → Option (Selection K) × ℕ) (xs : List α)
    (E : ℕ) (h : ∀ a ∈ xs,(evaluate a).2 ≤ E) :
    (scanRun evaluate xs).2 ≤ (E+12)*xs.length+2 := by
  induction xs with
  | nil => simp only [scanRun,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons a rest ih =>
    have ha := h a (by simp)
    have hr := ih (fun b hb => h b (by simp [hb]))
    change (evaluate a).2+(scanRun evaluate rest).2+8+4 ≤ _
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

def candidateRun {K S : ℕ} (field : Field K) (previous : FixedArrayTable (S+1) (Option (Selection K)))
    (s : Fin (S+1)) (label : Fin K) : Option (Selection K) × ℕ :=
  (candidate field previous s label,16)

def stepRun {K S : ℕ} (field : Field K) (previous : FixedArrayTable (S+1) (Option (Selection K))) :
    FixedArrayTable (S+1) (Option (Selection K)) × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 0) 1
    (fun s => scanRun (candidateRun field previous s) (List.finRange K))

theorem step_data {K S : ℕ} (field : Field K) (previous : FixedArrayTable (S+1) (Option (Selection K))) :
    (stepRun field previous).1=step field previous := by
  unfold stepRun step
  rw [PaperIndexedArrayConstruction.run_data]
  simp only [scan_data,candidateRun]

theorem step_work {K S : ℕ} (field : Field K) (previous : FixedArrayTable (S+1) (Option (Selection K))) :
    (stepRun field previous).2 ≤ 128*(S+1)*(K+1) := by
  have hEach (s : Fin (S+1)) :
      (scanRun (candidateRun field previous s) (List.finRange K)).2 ≤ 28*K+2 := by
    simpa only [List.length_finRange] using
      scan_work (candidateRun field previous s) (List.finRange K) 16 (fun _ _ => Nat.le_refl _)
  have hSum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hEach s)
  have hArray := PaperIndexedArrayConstruction.run_work_bound (fun _ => 0) 0 (fun _ => by simp) 1
    (fun s : Fin (S+1) => scanRun (candidateRun field previous s) (List.finRange K))
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul] at hSum
  change _ ≤ _+((S+1)+1)*(6+10*0*binaryWordWidth ((S+1)+1)+28) at hArray
  unfold stepRun
  nlinarith only [hSum,hArray]

def initialRun (K S : ℕ) : FixedArrayTable (S+1) (Option (Selection K)) × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 0) 1
    (fun s => (if s.val=0 then some ⟨0,[]⟩ else none,2))

theorem initial_data (K S : ℕ) : (initialRun K S).1=run (K:=K) S [] := by
  unfold initialRun run
  rw [PaperIndexedArrayConstruction.run_data]

theorem initial_work (K S : ℕ) : (initialRun K S).2 ≤ 128*(S+1)*(K+1) := by
  have hArray := PaperIndexedArrayConstruction.run_work_bound (fun _ => 0) 0 (fun _ => by simp) 1
    (fun s : Fin (S+1) => ((if s.val=0 then some (⟨0,[]⟩ : Selection K) else none),2))
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul] at hArray
  change _ ≤ (S+1)*2+((S+1)+1)*(6+10*0*binaryWordWidth ((S+1)+1)+28) at hArray
  unfold initialRun
  nlinarith only [hArray]

def runWithWork {K : ℕ} (S : ℕ) : List (Field K) → FixedArrayTable (S+1) (Option (Selection K)) × ℕ
  | [] => initialRun K S
  | field::rest =>
      let previous := runWithWork S rest
      let current := stepRun field previous.1
      (current.1,previous.2+current.2+4)

theorem run_data {K : ℕ} (S : ℕ) (fields : List (Field K)) : (runWithWork S fields).1=run S fields := by
  induction fields with
  | nil => exact initial_data K S
  | cons field rest ih =>
    change (stepRun field (runWithWork S rest).1).1=step field (run S rest)
    rw [step_data,ih]

theorem run_work {K : ℕ} (S : ℕ) (fields : List (Field K)) :
    (runWithWork S fields).2 ≤ 256*(fields.length+1)*(S+1)*(K+1) := by
  induction fields with
  | nil =>
    have h := initial_work K S
    change (initialRun K S).2 ≤ _
    simp only [List.length_nil,Nat.zero_add,Nat.mul_one]
    nlinarith only [h]
  | cons field rest ih =>
    have h := step_work field (runWithWork S rest).1
    change (runWithWork S rest).2+(stepRun field (runWithWork S rest).1).2+4 ≤ _
    simp only [List.length_cons]
    nlinarith only [ih,h]

end Blotto.GeneralPaperScoreDPWork
