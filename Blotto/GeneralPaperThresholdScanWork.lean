import Blotto.GeneralPaperBoundedQuotient
import Blotto.GeneralPaperScoreDPWork

/-! The final strict scan reads each materialized score cell once. A cell
uses its actual strict rational cost comparison, and a running integer max.
The declared unit profile includes array/reference/control fields. Actual
operand bit prices and simultaneous logical space are separate joins.
-/
namespace Blotto.GeneralPaperThresholdScanWork
open GeneralPaperMinimum GeneralPaperComputedThreshold
set_option autoImplicit false

def scan {K S : ℕ} (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) :
    List (Fin (S+1)) → ℕ × ℕ
  | [] => (0,2)
  | s::rest =>
      let current := acceptedScore table budget s
      let later := scan table budget rest
      (max current later.1,later.2+20)

theorem scan_data {K S : ℕ} (table : FixedArrayTable (S+1) (Option (Selection K)))
    (budget : ℚ) (xs : List (Fin (S+1))) :
    (scan table budget xs).1=xs.toFinset.sup (acceptedScore table budget) := by
  induction xs with
  | nil => simp only [scan,List.toFinset_nil,Finset.sup_empty]; rfl
  | cons s rest ih =>
    simp only [scan,List.toFinset_cons,Finset.sup_insert,ih]

theorem scan_work {K S : ℕ} (table : FixedArrayTable (S+1) (Option (Selection K)))
    (budget : ℚ) (xs : List (Fin (S+1))) : (scan table budget xs).2=20*xs.length+2 := by
  induction xs with
  | nil => rfl
  | cons s rest ih => simp only [scan,List.length_cons,ih]; omega

def run {K S : ℕ} (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) : ℕ × ℕ :=
  let result := scan table budget (List.finRange (S+1))
  (result.1,result.2+4*(S+1)+4)

theorem run_data {K S : ℕ} (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) :
    (run table budget).1=scanThreshold table budget := by
  rw [run,scan_data]
  have h : (List.finRange (S+1)).toFinset=Finset.univ := by ext i; simp
  rw [h]
  rfl

theorem run_work {K S : ℕ} (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) :
    (run table budget).2≤32*(S+1)+8 := by
  simp only [run,scan_work,List.length_finRange]
  omega

end Blotto.GeneralPaperThresholdScanWork
