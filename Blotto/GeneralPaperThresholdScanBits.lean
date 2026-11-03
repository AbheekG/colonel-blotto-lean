import Blotto.GeneralPaperQuantizedHeight

/-! The final strict score scan with actual rational comparison prices.
The old budget's height and actual retained partial-resource widths jointly
bound comparison operands. Source score/index words are checked by the caller.
-/
namespace Blotto.GeneralPaperThresholdScanBits
open GeneralPaperMinimum GeneralPaperExactScoreDP GeneralPaperComputedThreshold
open GeneralPaperScoreBitPrimitive GeneralPaperBoundedQuotient
set_option autoImplicit false
set_option maxHeartbeats 1500000

def acceptedRun {K S : ℕ} (model : RationalCostModel) (W : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) (s : Fin (S+1)) : ℕ × ℕ :=
  match table.read s with
  | none => (0,16*W)
  | some chosen => (if chosen.cost<budget then s.val else 0,
      16*W+primitivePrice model chosen.cost budget)

theorem accepted_data {K S : ℕ} (model : RationalCostModel) (W : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) (s : Fin (S+1)) :
    (acceptedRun model W table budget s).1=acceptedScore table budget s := by
  unfold acceptedRun acceptedScore
  cases table.read s <;> rfl

theorem accepted_work {K S : ℕ} (model : RationalCostModel) (W H : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) (s : Fin (S+1))
    (hTable : Width (table.read s) H) (hBudget : rationalWordWidth budget≤H) :
    (acceptedRun model W table budget s).2≤16*W+model.rat H := by
  unfold acceptedRun
  cases he : table.read s with
  | none => simp only; omega
  | some chosen =>
    have hp := primitivePrice_le model chosen.cost budget H (hTable chosen he) hBudget
    exact Nat.add_le_add_left hp _

def scanRun {K S : ℕ} (model : RationalCostModel) (W : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) :
    List (Fin (S+1)) → ℕ × ℕ
  | [] => (0,2*W)
  | s::rest =>
      let current := acceptedRun model W table budget s
      let later := scanRun model W table budget rest
      (max current.1 later.1,current.2+later.2+8*W)

theorem scan_data {K S : ℕ} (model : RationalCostModel) (W : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) (xs : List (Fin (S+1))) :
    (scanRun model W table budget xs).1=xs.toFinset.sup (acceptedScore table budget) := by
  induction xs with
  | nil => simp only [scanRun,List.toFinset_nil,Finset.sup_empty]; rfl
  | cons s rest ih => simp only [scanRun,accepted_data,ih,List.toFinset_cons,Finset.sup_insert]

theorem scan_work {K S : ℕ} (model : RationalCostModel) (W H : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) (xs : List (Fin (S+1)))
    (hTable : ∀ s,Width (table.read s) H) (hBudget : rationalWordWidth budget≤H) :
    (scanRun model W table budget xs).2≤(24*W+model.rat H)*xs.length+2*W := by
  induction xs with
  | nil => simp only [scanRun,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons s rest ih =>
    have hc := accepted_work model W H table budget s (hTable s) hBudget
    change (acceptedRun model W table budget s).2+(scanRun model W table budget rest).2+8*W≤_
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

def runWithBits {K S : ℕ} (model : RationalCostModel) (W : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) : ℕ × ℕ :=
  let result := scanRun model W table budget (List.finRange (S+1))
  (result.1,result.2+4*(S+1)*W+4*W)

theorem run_data {K S : ℕ} (model : RationalCostModel) (W : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) :
    (runWithBits model W table budget).1=scanThreshold table budget := by
  rw [runWithBits,scan_data]
  have h : (List.finRange (S+1)).toFinset=Finset.univ := by ext s; simp
  rw [h]
  rfl

def comparisonWidth (A r B : ℕ) : ℕ := resourceWidth A r+(1+2*B)

def profile (model : RationalCostModel) (W S A r B : ℕ) : ℕ :=
  (S+1)*(28*W+model.rat (comparisonWidth A r B))+6*W

theorem run_work {K : ℕ} (model : RationalCostModel) (W A B S : ℕ) (fields : List (Field K))
    (hFields : CostHeight fields A) (budget : ℚ) (hBudget : RationalHeight budget B) :
    (runWithBits model W (run S fields) budget).2≤profile model W S A fields.length B := by
  have hTable (s : Fin (S+1)) : Width ((run S fields).read s) (comparisonWidth A fields.length B) := by
    intro chosen hc
    have h := run_some_width S fields A hFields s chosen hc
    exact h.trans (Nat.le_add_right _ _)
  have hb : rationalWordWidth budget≤comparisonWidth A fields.length B :=
    (rationalWordWidth_of_height hBudget).trans (Nat.le_add_left _ _)
  have h := scan_work model W (comparisonWidth A fields.length B) (run S fields) budget
    (List.finRange (S+1)) hTable hb
  simp only [List.length_finRange] at h
  change (scanRun model W (run S fields) budget (List.finRange (S+1))).2+4*(S+1)*W+4*W≤_
  unfold profile
  nlinarith only [h]

end Blotto.GeneralPaperThresholdScanBits
