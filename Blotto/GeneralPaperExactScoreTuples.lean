import Blotto.GeneralPaperExactScoreDP

/-! Stored DP witnesses correspond to actual labelled field tuples, in
their original order, with exact total score and rational resource sum.
-/
namespace Blotto.GeneralPaperExactScoreDP
open GeneralPaperMinimum
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000

def fields {m K : ℕ} (profits : Fin m → Fin K → ℕ) (costs : Fin m → Fin K → ℚ) : List (Field K) :=
  List.ofFn (fun j => FixedArrayTable.ofFn (fun l => (profits j l,costs j l)))

theorem fits_cons {K : ℕ} (field : Field K) (rest : List (Field K)) (label : Fin K)
    (s : ℕ) (tail : Selection K) (h : Fits rest s tail) :
    Fits (field::rest) ((field.read label).1+s) (extend label (field.read label).2 tail) := by
  refine ⟨label,by omega,tail,?_,rfl⟩
  simpa only [Nat.add_sub_cancel_left] using h

theorem fits_of_tuple {m K : ℕ} (profits : Fin m → Fin K → ℕ) (costs : Fin m → Fin K → ℚ)
    (labels : Fin m → Fin K) :
    Fits (fields profits costs) (∑ j,profits j (labels j)) ⟨∑ j,costs j (labels j),List.ofFn labels⟩ := by
  induction m with
  | zero => simp only [fields,List.ofFn_zero,Fits,Finset.univ_eq_empty,Finset.sum_empty,and_self]
  | succ m ih =>
    have hi := ih (fun j : Fin m => profits j.succ) (fun j : Fin m => costs j.succ) (fun j : Fin m => labels j.succ)
    have h := fits_cons (FixedArrayTable.ofFn (fun l => (profits 0 l,costs 0 l)))
      (fields (fun j : Fin m => profits j.succ) (fun j : Fin m => costs j.succ)) (labels 0)
      (∑ j : Fin m,profits j.succ (labels j.succ))
      ⟨∑ j : Fin m,costs j.succ (labels j.succ),List.ofFn (fun j : Fin m => labels j.succ)⟩ hi
    simpa only [fields,List.ofFn_succ,Fin.sum_univ_succ,FixedArrayTable.read_ofFn,extend] using h

theorem tuple_of_fits {m K : ℕ} (profits : Fin m → Fin K → ℕ) (costs : Fin m → Fin K → ℚ)
    (s : ℕ) (chosen : Selection K) (h : Fits (fields profits costs) s chosen) :
    ∃ labels : Fin m → Fin K,(∑ j,profits j (labels j))=s ∧
      (∑ j,costs j (labels j))=chosen.cost ∧ List.ofFn labels=chosen.labels := by
  induction m generalizing s chosen with
  | zero =>
    have he : s=0 ∧ chosen=⟨0,[]⟩ := h
    refine ⟨Fin.elim0,?_⟩
    simp only [Finset.univ_eq_empty,Finset.sum_empty,List.ofFn_zero,he.1,he.2,and_self]
  | succ m ih =>
    simp only [fields,List.ofFn_succ,Fits,FixedArrayTable.read_ofFn] at h
    obtain ⟨label,hScore,tail,hTail,hChosen⟩ := h
    have hTail' : Fits (fields (fun j : Fin m => profits j.succ) (fun j : Fin m => costs j.succ))
        (s-profits 0 label) tail := hTail
    obtain ⟨labels,hs,hc,hl⟩ := ih (fun j : Fin m => profits j.succ) (fun j : Fin m => costs j.succ) _ tail hTail'
    refine ⟨Fin.cons label labels,?_,?_,?_⟩
    · simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
      omega
    · rw [hChosen]
      simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,extend,hc]
    · rw [hChosen]
      simp only [List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,extend,hl]

end Blotto.GeneralPaperExactScoreDP
