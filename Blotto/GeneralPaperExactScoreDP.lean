import Blotto.GeneralPaperMinimum
import Blotto.FixedArrayTable

/-! Exact-score DP in actual stored arrays. A cell is absent or retains a
rational minimum cost and a shared predecessor-label list. Each new layer
reads one previous layer, considers K options per score, and is materialized
once. No tuple enumeration or recursively recomputed cell is executed.
The reference predicate is erased and ranges over all actual tuples.
-/
namespace Blotto.GeneralPaperExactScoreDP
open GeneralPaperMinimum
set_option autoImplicit false
set_option maxHeartbeats 1500000

abbrev Field (K : ℕ) := FixedArrayTable K (ℕ × ℚ)

def Fits {K : ℕ} : List (Field K) → ℕ → Selection K → Prop
  | [],s,chosen => s=0 ∧ chosen=⟨0,[]⟩
  | field::rest,s,chosen => ∃ label : Fin K,(field.read label).1 ≤ s ∧
      ∃ tail,Fits rest (s-(field.read label).1) tail ∧ chosen=extend label (field.read label).2 tail

def Via {K : ℕ} (field : Field K) (rest : List (Field K)) (s : ℕ) (label : Fin K)
    (chosen : Selection K) : Prop :=
  (field.read label).1 ≤ s ∧ ∃ tail,Fits rest (s-(field.read label).1) tail ∧
    chosen=extend label (field.read label).2 tail

def candidate {K S : ℕ} (field : Field K) (previous : FixedArrayTable (S+1) (Option (Selection K)))
    (s : Fin (S+1)) (label : Fin K) : Option (Selection K) :=
  let data := field.read label
  if h : data.1 ≤ s.val then
    (previous.read ⟨s.val-data.1,by omega⟩).map (extend label data.2)
  else none

def step {K S : ℕ} (field : Field K) (previous : FixedArrayTable (S+1) (Option (Selection K))) :
    FixedArrayTable (S+1) (Option (Selection K)) :=
  FixedArrayTable.ofFn (fun s => scan (candidate field previous s) (List.finRange K))

def run {K : ℕ} (S : ℕ) : List (Field K) → FixedArrayTable (S+1) (Option (Selection K))
  | [] => FixedArrayTable.ofFn (fun s => if s.val=0 then some ⟨0,[]⟩ else none)
  | field::rest => step field (run S rest)

theorem candidate_best {K S : ℕ} (field : Field K) (rest : List (Field K))
    (previous : FixedArrayTable (S+1) (Option (Selection K)))
    (hPrevious : ∀ s,Best (Fits rest s.val) (previous.read s)) (s : Fin (S+1)) (label : Fin K) :
    Best (Via field rest s.val label) (candidate field previous s label) := by
  unfold candidate
  dsimp only
  split
  · rename_i hScore
    let index : Fin (S+1) := ⟨s.val-(field.read label).1,by omega⟩
    have hp := hPrevious index
    cases he : previous.read index with
    | none =>
      rw [he] at hp
      intro chosen hChosen
      obtain ⟨_,tail,hTail,_⟩ := hChosen
      exact hp tail hTail
    | some tail =>
      rw [he] at hp
      refine ⟨⟨hScore,tail,hp.1,rfl⟩,?_⟩
      intro chosen hChosen
      obtain ⟨_,other,hOther,rfl⟩ := hChosen
      change (field.read label).2+tail.cost ≤ (field.read label).2+other.cost
      have hh := hp.2 other hOther
      linarith only [hh]
  · rename_i hScore
    intro chosen hChosen
    exact hScore hChosen.1

theorem step_best {K S : ℕ} (field : Field K) (rest : List (Field K))
    (previous : FixedArrayTable (S+1) (Option (Selection K)))
    (hPrevious : ∀ s,Best (Fits rest s.val) (previous.read s)) (s : Fin (S+1)) :
    Best (Fits (field::rest) s.val) ((step field previous).read s) := by
  rw [step,FixedArrayTable.read_ofFn]
  have h := scan_best (candidate field previous s) (Via field rest s.val) (List.finRange K)
    (fun label _ => candidate_best field rest previous hPrevious s label)
  have he : (fun chosen => ∃ label ∈ List.finRange K,Via field rest s.val label chosen)=
      Fits (field::rest) s.val := by
    funext chosen
    apply propext
    simp only [List.mem_finRange,true_and,Fits,Via]
  rw [he] at h
  exact h

theorem run_best {K : ℕ} (S : ℕ) (fields : List (Field K)) (s : Fin (S+1)) :
    Best (Fits fields s.val) ((run S fields).read s) := by
  induction fields generalizing s with
  | nil =>
    rw [run,FixedArrayTable.read_ofFn]
    split
    · rename_i hs
      refine ⟨⟨hs,rfl⟩,?_⟩
      intro chosen hChosen
      rw [hChosen.2]
    · rename_i hs
      intro chosen hChosen
      exact hs hChosen.1
  | cons field rest ih =>
    exact step_best field rest (run S rest) (fun s => ih s) s

theorem fits_length {K : ℕ} (fields : List (Field K)) (s : ℕ) (chosen : Selection K)
    (h : Fits fields s chosen) : chosen.labels.length=fields.length := by
  induction fields generalizing s chosen with
  | nil => rw [h.2]; rfl
  | cons field rest ih =>
    obtain ⟨label,_,tail,hTail,rfl⟩ := h
    simp only [extend,List.length_cons]
    exact congrArg Nat.succ (ih _ _ hTail)

end Blotto.GeneralPaperExactScoreDP
