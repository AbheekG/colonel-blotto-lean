import Blotto.GeneralPaperStaticRaySound

/-! A fixed-point high-tuple query executes one complete stored exact-score
DP and scans its S+1 cells. The strict score test is h<s; a missing score
does not block. Whole tuples occur only in the erased specification.
-/
namespace Blotto.GeneralPaperRayHighMinimum
open GeneralPaperMinimum GeneralPaperExactScoreDP
set_option autoImplicit false
set_option maxHeartbeats 2500000

def candidate {K S : ℕ} (table : FixedArrayTable (S+1) (Option (Selection K))) (h : ℕ)
    (s : Fin (S+1)) : Option (Selection K) := if h<s.val then table.read s else none

def minimum {m K : ℕ} (scores : Fin m → Fin K → ℕ) (costs : Fin m → Fin K → ℚ) (S h : ℕ) : Option (Selection K) :=
  let table := run S (fields scores costs)
  scan (candidate table h) (List.finRange (S+1))

def Selected {m K : ℕ} (scores : Fin m → Fin K → ℕ) (costs : Fin m → Fin K → ℚ) (S h : ℕ)
    (chosen : Selection K) : Prop := ∃ s : Fin (S+1),h<s.val ∧ Fits (fields scores costs) s.val chosen

theorem candidate_best {m K S : ℕ} (scores : Fin m → Fin K → ℕ) (costs : Fin m → Fin K → ℚ)
    (h : ℕ) (s : Fin (S+1)) :
    Best (fun chosen => h<s.val ∧ Fits (fields scores costs) s.val chosen)
      (candidate (run S (fields scores costs)) h s) := by
  have hb := run_best S (fields scores costs) s
  unfold candidate
  split
  · rename_i hs
    cases he : (run S (fields scores costs)).read s with
    | none => rw [he] at hb; exact fun chosen hc => hb chosen hc.2
    | some chosen => rw [he] at hb; exact ⟨⟨hs,hb.1⟩,fun other ho => hb.2 other ho.2⟩
  · rename_i hs
    exact fun chosen hc => hs hc.1

theorem minimum_best {m K : ℕ} (scores : Fin m → Fin K → ℕ) (costs : Fin m → Fin K → ℚ) (S h : ℕ) :
    Best (Selected scores costs S h) (minimum scores costs S h) := by
  have hb := scan_best (candidate (run S (fields scores costs)) h)
    (fun s chosen => h<s.val ∧ Fits (fields scores costs) s.val chosen) (List.finRange (S+1))
    (fun s _ => candidate_best scores costs h s)
  have he : (fun chosen => ∃ s ∈ List.finRange (S+1),h<s.val ∧ Fits (fields scores costs) s.val chosen)=
      Selected scores costs S h := by
    funext chosen
    apply propext
    simp only [Selected,List.mem_finRange,true_and]
  rw [he] at hb
  exact hb

def passes {m K : ℕ} (scores : Fin m → Fin K → ℕ) (costs : Fin m → Fin K → ℚ) (S h : ℕ) (beta : ℚ) : Bool :=
  match minimum scores costs S h with
  | none => true
  | some chosen => decide (beta≤chosen.cost)

end Blotto.GeneralPaperRayHighMinimum
