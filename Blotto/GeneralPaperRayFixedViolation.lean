import Blotto.GeneralPaperRayFinalBudget

/-! Recover a violating high-score cell from the FIXED affine predecessor
table with one score scan. No whole-tuple search or additional full DP is
executed. The retained choice includes its original predecessor labels.
-/
namespace Blotto.GeneralPaperRayFixedViolation
open GeneralPaperRayAffineMinimum GeneralPaperRayAffineScoreStep GeneralPaperRayTableFeasibility
set_option autoImplicit false
set_option maxHeartbeats 3500000

abbrev Entry (S K : ℕ) := Fin (S+1) × Choice K

def candidate {S K : ℕ} (table : Table S K) (h : ℕ) (beta t : ℚ) (s : Fin (S+1)) : Option (Entry S K) :=
  if h<s.val then
    match table.read s with
    | none => none
    | some c => if c.expression.value t<beta then some (s,c) else none
  else none

def Valid {S K : ℕ} (table : Table S K) (h : ℕ) (beta t : ℚ) (entry : Entry S K) : Prop :=
  h<entry.1.val ∧ table.read entry.1=some entry.2 ∧ entry.2.expression.value t<beta

structure Result (S K : ℕ) where
  value : Option (Entry S K)
  work : ℕ

def scan {S K : ℕ} (table : Table S K) (h : ℕ) (beta t : ℚ) : List (Fin (S+1)) → Result S K
  | [] => ⟨none,2⟩
  | s::rest =>
    match candidate table h beta t s with
    | some entry => ⟨some entry,32⟩
    | none =>
      let later := scan table h beta t rest
      ⟨later.value,later.work+32⟩

def run {S K : ℕ} (table : Table S K) (h : ℕ) (beta t : ℚ) : Result S K := scan table h beta t (List.finRange (S+1))

theorem candidate_valid {S K : ℕ} (table : Table S K) (h : ℕ) (beta t : ℚ)
    (s : Fin (S+1)) (entry : Entry S K) (hc : candidate table h beta t s=some entry) : Valid table h beta t entry := by
  unfold candidate at hc
  split at hc
  · rename_i hs
    cases he : table.read s with
    | none => rw [he] at hc; contradiction
    | some c =>
      rw [he] at hc
      change (if c.expression.value t<beta then some (s,c) else none)=some entry at hc
      split at hc
      · rename_i hp
        have hh : (s,c)=entry := Option.some.inj hc
        subst entry
        exact ⟨hs,he,hp⟩
      · contradiction
  · contradiction

theorem scan_valid {S K : ℕ} (table : Table S K) (h : ℕ) (beta t : ℚ) (xs : List (Fin (S+1)))
    (entry : Entry S K) (hc : (scan table h beta t xs).value=some entry) : Valid table h beta t entry := by
  induction xs with
  | nil => contradiction
  | cons s rest ih =>
    rw [scan] at hc
    cases he : candidate table h beta t s with
    | none => rw [he] at hc; exact ih hc
    | some c =>
      rw [he] at hc
      have hh : c=entry := Option.some.inj hc
      subst c
      exact candidate_valid table h beta t s entry he

theorem scan_exists {S K : ℕ} (table : Table S K) (h : ℕ) (beta t : ℚ) (xs : List (Fin (S+1)))
    (s : Fin (S+1)) (hs : s∈xs) (entry : Entry S K) (hc : candidate table h beta t s=some entry) :
    ∃ out,(scan table h beta t xs).value=some out := by
  induction xs with
  | nil => contradiction
  | cons j rest ih =>
    cases he : candidate table h beta t j with
    | some c => exact ⟨c,by simp only [scan,he]⟩
    | none =>
      have ht : s∈rest := by
        rcases List.mem_cons.mp hs with hh|hh
        · subst s; rw [he] at hc; contradiction
        · exact hh
      obtain ⟨out,hOut⟩ := ih ht
      exact ⟨out,by simpa only [scan,he] using hOut⟩

theorem run_exists {S K : ℕ} (table : Table S K) (h : ℕ) (beta t : ℚ)
    (hNot : ¬TableFeasible table h beta t) : ∃ entry,(run table h beta t).value=some entry := by
  classical
  simp only [TableFeasible] at hNot
  push Not at hNot
  obtain ⟨s,hs,c,hc,hp⟩ := hNot
  apply scan_exists table h beta t (List.finRange (S+1)) s (List.mem_finRange _) (s,c)
  simp only [candidate,hs,ite_true,hc,hp]

theorem scan_work {S K : ℕ} (table : Table S K) (h : ℕ) (beta t : ℚ) (xs : List (Fin (S+1))) :
    (scan table h beta t xs).work≤32*xs.length+2 := by
  induction xs with
  | nil => exact le_rfl
  | cons s rest ih =>
    rw [scan]
    split <;> dsimp only
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega

theorem run_work {S K : ℕ} (table : Table S K) (h : ℕ) (beta t : ℚ) : (run table h beta t).work≤32*(S+1)+2 := by
  simpa only [run,List.length_finRange] using scan_work table h beta t (List.finRange (S+1))

end Blotto.GeneralPaperRayFixedViolation
