import Blotto.GeneralPaperScoreBitPrimitive

/-! The stored score DP with actual rational bit prices and source word
traffic. Data erase to the same indexed DP. W must cover source references,
loop words and stored scores; score/index capacity is checked separately.
The array constructor pays its linear integer-word primitive and reference
profile. These are the paper's bit-model prices, not native allocator rates.
-/
namespace Blotto.GeneralPaperScoreDPBits
open GeneralPaperMinimum GeneralPaperExactScoreDP GeneralPaperScoreBitPrimitive
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000

def stepRun {K S : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K)
    (previous : FixedArrayTable (S+1) (Option (Selection K))) :
    FixedArrayTable (S+1) (Option (Selection K)) × ℕ :=
  PaperIndexedArrayConstruction.run (fun w => w) W
    (fun s => scanRun model W (candidateRun model W field previous s) (List.finRange K))

theorem step_data {K S : ℕ} (model : RationalCostModel) (W : ℕ) (field : Field K)
    (previous : FixedArrayTable (S+1) (Option (Selection K))) :
    (stepRun model W field previous).1=step field previous := by
  unfold stepRun step
  rw [PaperIndexedArrayConstruction.run_data]
  simp only [scan_data,candidate_data]

def stepProfile (K S W P : ℕ) : ℕ :=
  (S+1)*((76*W+3*P)*K+2*W)+88*(S+1)*W

theorem stepProfile_mono (K S W : ℕ) {P Q : ℕ} (h : P≤Q) : stepProfile K S W P≤stepProfile K S W Q := by
  unfold stepProfile
  gcongr

theorem array_overhead (S W : ℕ) (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    (S+2)*(6*W+10*binaryWordWidth (S+2)+28)≤88*(S+1)*W := by
  have hPrice : 6*W+10*binaryWordWidth (S+2)+28≤44*W := by omega
  calc
    _ ≤ (S+2)*(44*W) := Nat.mul_le_mul_left _ hPrice
    _ ≤ (2*(S+1))*(44*W) := Nat.mul_le_mul_right _ (by omega : S+2≤2*(S+1))
    _ = _ := by ring

theorem step_work {K S : ℕ} (model : RationalCostModel) (W A : ℕ) (field : Field K) (rest : List (Field K))
    (hFields : CostHeight (field::rest) A) (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    (stepRun model W field (run S rest)).2≤stepProfile K S W (model.rat (resourceWidth A (rest.length+1))) := by
  let P := model.rat (resourceWidth A (rest.length+1))
  have hEach (s : Fin (S+1)) :
      (scanRun model W (candidateRun model W field (run S rest) s) (List.finRange K)).2≤(76*W+3*P)*K+2*W := by
    have h := scan_work model W (resourceWidth A (rest.length+1)) (64*W+2*P)
      (candidateRun model W field (run S rest) s) (List.finRange K)
      (fun l _ => candidate_width model W A field rest hFields s l)
      (fun l _ => candidate_work model W A field rest hFields s l)
    simp only [List.length_finRange] at h
    convert h using 1 <;> dsimp only [P] <;> ring
  have hSum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hEach s)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hSum
  have hArray := PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W
    (fun s => scanRun model W (candidateRun model W field (run S rest) s) (List.finRange K))
  change (stepRun model W field (run S rest)).2≤
    (∑ s,(scanRun model W (candidateRun model W field (run S rest) s) (List.finRange K)).2)+
      (S+2)*(6*W+10*binaryWordWidth (S+2)+28) at hArray
  unfold stepProfile
  exact hArray.trans (Nat.add_le_add hSum (array_overhead S W hW hIndex))

def initialRun (model : RationalCostModel) (W K S : ℕ) : FixedArrayTable (S+1) (Option (Selection K)) × ℕ :=
  PaperIndexedArrayConstruction.run (fun w => w) W
    (fun s => (if s.val=0 then some ⟨0,[]⟩ else none,2*W+3))

theorem initial_data (model : RationalCostModel) (W K S : ℕ) :
    (initialRun model W K S).1=run (K:=K) S [] := by
  unfold initialRun run
  rw [PaperIndexedArrayConstruction.run_data]

def initialProfile (S W : ℕ) : ℕ := (S+1)*(2*W+3)+88*(S+1)*W

theorem initial_work (model : RationalCostModel) (W K S : ℕ) (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    (initialRun model W K S).2 ≤ initialProfile S W := by
  unfold initialRun
  apply (PaperIndexedArrayConstruction.run_work_bound (fun w => w) 1 (fun _ => by omega) W
    (fun s : Fin (S+1) => ((if s.val=0 then some (⟨0,[]⟩ : Selection K) else none),2*W+3))).trans
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_one]
  unfold initialProfile
  exact Nat.add_le_add_left (array_overhead S W hW hIndex) _

def runWithBits {K : ℕ} (model : RationalCostModel) (W S : ℕ) :
    List (Field K) → FixedArrayTable (S+1) (Option (Selection K)) × ℕ
  | [] => initialRun model W K S
  | field::rest =>
      let previous := runWithBits model W S rest
      let current := stepRun model W field previous.1
      (current.1,previous.2+current.2+4*W)

theorem run_data {K : ℕ} (model : RationalCostModel) (W S : ℕ) (fields : List (Field K)) :
    (runWithBits model W S fields).1=run S fields := by
  induction fields with
  | nil => exact initial_data model W K S
  | cons field rest ih =>
    change (stepRun model W field (runWithBits model W S rest).1).1=step field (run S rest)
    rw [step_data,ih]

def profile (r K S W P : ℕ) : ℕ := initialProfile S W+r*(stepProfile K S W P+4*W)

theorem run_work {K : ℕ} (model : RationalCostModel) (W A S : ℕ) (fields : List (Field K))
    (hFields : CostHeight fields A) (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    (runWithBits model W S fields).2≤profile fields.length K S W (model.rat (resourceWidth A fields.length)) := by
  induction fields with
  | nil =>
    simpa only [runWithBits,profile,List.length_nil,Nat.zero_mul,Nat.add_zero] using initial_work model W K S hW hIndex
  | cons field rest ih =>
    have hp := ih (fun f hf => hFields f (by simp [hf]))
    have hm := stepProfile_mono K S W (model.monotone (resourceWidth_mono A (Nat.le_succ rest.length)))
    have hPrevious := hp.trans (Nat.add_le_add_left (Nat.mul_le_mul_left rest.length (Nat.add_le_add_right hm (4*W))) _)
    have hStep := step_work model W A field rest hFields hW hIndex
    have hStepActual : (stepRun model W field (runWithBits model W S rest).1).2≤
        stepProfile K S W (model.rat (resourceWidth A (rest.length+1))) := by
      rw [run_data]
      exact hStep
    change (runWithBits model W S rest).2+(stepRun model W field (runWithBits model W S rest).1).2+4*W≤_
    unfold profile at *
    simp only [List.length_cons]
    nlinarith only [hPrevious,hStepActual]

def ScoresBound {K : ℕ} (fields : List (Field K)) (S : ℕ) : Prop :=
  ∀ f ∈ fields,∀ l,(f.read l).1≤S

theorem score_words {K : ℕ} (fields : List (Field K)) (S W : ℕ) (h : ScoresBound fields S)
    (hIndex : binaryWordWidth (S+2)≤W) (f : Field K) (hf : f ∈ fields) (l : Fin K) :
    binaryWordWidth (f.read l).1≤W :=
  (binaryWordWidth_mono ((h f hf l).trans (by omega))).trans hIndex

theorem score_index_words (S W : ℕ) (hIndex : binaryWordWidth (S+2)≤W) (s : Fin (S+1)) :
    binaryWordWidth s.val≤W := (binaryWordWidth_mono (by omega)).trans hIndex

theorem label_words (K W : ℕ) (hLabel : binaryWordWidth (K+2)≤W) (l : Fin K) :
    binaryWordWidth l.val≤W := (binaryWordWidth_mono (by omega)).trans hLabel

end Blotto.GeneralPaperScoreDPBits
