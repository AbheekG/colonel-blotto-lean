import Blotto.GeneralPaperRayHighMinimum

/-! The executed high-score minimum decides every high-tuple inequality,
including equality. Failure retains a strict violating tuple, in original
field order, through the stored predecessor labels.
-/
namespace Blotto.GeneralPaperRayHighSound
open GeneralPaperMinimum GeneralPaperExactScoreDP GeneralPaperRayHighMinimum
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000

def HighFeasible {m K : ℕ} (scores : Fin m → Fin K → ℕ) (costs : Fin m → Fin K → ℚ) (h : ℕ) (beta : ℚ) : Prop :=
  ∀ labels : Fin m → Fin K,h<(∑ j,scores j (labels j)) → beta≤∑ j,costs j (labels j)

theorem selected_witness {m K : ℕ} (scores : Fin m → Fin K → ℕ) (costs : Fin m → Fin K → ℚ)
    (S h : ℕ) (chosen : Selection K) (hc : minimum scores costs S h=some chosen) :
    ∃ labels : Fin m → Fin K,h<(∑ j,scores j (labels j)) ∧
      (∑ j,costs j (labels j))=chosen.cost ∧ List.ofFn labels=chosen.labels := by
  have hb := minimum_best scores costs S h
  rw [hc] at hb
  obtain ⟨s,hs,hFits⟩ := hb.1
  obtain ⟨labels,hScore,hCost,hLabels⟩ := tuple_of_fits scores costs s.val chosen hFits
  exact ⟨labels,by omega,hCost,hLabels⟩

theorem minimum_le_tuple {m K : ℕ} (scores : Fin m → Fin K → ℕ) (costs : Fin m → Fin K → ℚ)
    (S h : ℕ) (hCap : ∀ labels : Fin m → Fin K,(∑ j,scores j (labels j))≤S)
    (labels : Fin m → Fin K) (hHigh : h<(∑ j,scores j (labels j))) :
    ∃ chosen,minimum scores costs S h=some chosen ∧ chosen.cost≤∑ j,costs j (labels j) := by
  let s : Fin (S+1) := ⟨∑ j,scores j (labels j),by have hh := hCap labels; omega⟩
  let witness : Selection K := ⟨∑ j,costs j (labels j),List.ofFn labels⟩
  have hw : Selected scores costs S h witness := ⟨s,hHigh,fits_of_tuple scores costs labels⟩
  have hb := minimum_best scores costs S h
  cases hc : minimum scores costs S h with
  | none => rw [hc] at hb; exact (hb witness hw).elim
  | some chosen => rw [hc] at hb; exact ⟨chosen,rfl,hb.2 witness hw⟩

theorem passes_iff {m K : ℕ} (scores : Fin m → Fin K → ℕ) (costs : Fin m → Fin K → ℚ)
    (S h : ℕ) (hCap : ∀ labels : Fin m → Fin K,(∑ j,scores j (labels j))≤S) (beta : ℚ) :
    passes scores costs S h beta=true ↔ HighFeasible scores costs h beta := by
  constructor
  · intro hp labels hHigh
    obtain ⟨chosen,hc,hMin⟩ := minimum_le_tuple scores costs S h hCap labels hHigh
    have hh : beta≤chosen.cost := by simpa only [passes,hc,decide_eq_true_eq] using hp
    exact hh.trans hMin
  · intro hf
    cases hc : minimum scores costs S h with
    | none => simp only [passes,hc]
    | some chosen =>
      obtain ⟨labels,hHigh,hCost,_⟩ := selected_witness scores costs S h chosen hc
      have hh := hf labels hHigh
      rw [hCost] at hh
      simpa only [passes,hc,decide_eq_true_eq] using hh

theorem failed_witness {m K : ℕ} (scores : Fin m → Fin K → ℕ) (costs : Fin m → Fin K → ℚ)
    (S h : ℕ) (beta : ℚ) (hp : passes scores costs S h beta=false) :
    ∃ chosen labels,minimum scores costs S h=some chosen ∧
      h<(∑ j,scores j (labels j)) ∧ (∑ j,costs j (labels j))<beta ∧
      (∑ j,costs j (labels j))=chosen.cost ∧ List.ofFn labels=chosen.labels := by
  cases hc : minimum scores costs S h with
  | none => simp only [passes,hc,Bool.true_eq_false] at hp
  | some chosen =>
    have hh : chosen.cost<beta := by
      have hn : ¬beta≤chosen.cost := by simpa only [passes,hc,decide_eq_false_iff_not] using hp
      exact lt_of_not_ge hn
    obtain ⟨labels,hHigh,hCost,hLabels⟩ := selected_witness scores costs S h chosen hc
    exact ⟨chosen,labels,rfl,hHigh,by rwa [hCost],hCost,hLabels⟩

end Blotto.GeneralPaperRayHighSound
