import Blotto.GeneralPaperRayFixedViolation

/-! The fixed affine predecessor labels recover one original whole tuple.
Its sum equals the retained affine expression at EVERY rational parameter,
including both closed endpoints. Native decoding converts the shared label
list once into an indexed row; its shape guard is derived from DP validity.
-/
namespace Blotto.GeneralPaperRayFixedTuple
open RationalOrderCell GeneralPaperRayAffine GeneralPaperRayAffineMinimum GeneralPaperRayAffineScoreStep GeneralPaperRayAnchorCosts
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

def decode {K : ℕ} (m : ℕ) (chosen : Choice K) : Option (FixedArrayTable m (Fin K)) :=
  if h : chosen.labels.length=m then some ⟨chosen.labels.toArray,by simp only [List.size_toArray,h]⟩ else none

theorem decode_labels {m K : ℕ} (chosen : Choice K) (labels : Fin m → Fin K) (hLabels : List.ofFn labels=chosen.labels) :
    ∃ row,decode m chosen=some row ∧ row.read=labels := by
  have hLength : chosen.labels.length=m := by rw [←hLabels]; exact List.length_ofFn
  let row : FixedArrayTable m (Fin K) := ⟨chosen.labels.toArray,by simp only [List.size_toArray,hLength]⟩
  refine ⟨row,by simp only [decode,hLength,dite_true]; rfl,?_⟩
  funext j
  simp only [row,FixedArrayTable.read,←hLabels,List.getElem_toArray,List.getElem_ofFn]

theorem tuple_everywhere {m S K : ℕ} (scores : Fin m → Fin K → ℕ) (x w : Variable m K → ℚ)
    (table : Table S K) (lo hi : ℚ) (hOrder : lo<hi) (s : Fin (S+1)) (chosen : Choice K) (hc : table.read s=some chosen)
    (hBest : ∀ t,lo<t ∧ t<hi → ∀ q,GeneralPaperMinimum.Best (GeneralPaperExactScoreDP.Fits
      (GeneralPaperExactScoreDP.fields scores (costs x w t)) q.val) ((tableAt table t).read q)) :
    ∃ labels : Fin m → Fin K,(∑ j,scores j (labels j))=s.val ∧ List.ofFn labels=chosen.labels ∧
      ∀ t,(∑ j,costs x w t j (labels j))=chosen.expression.value t := by
  let sample := (lo+hi)/2
  have hSample := GeneralPaperRayStableMinimum.midpoint_inside lo hi hOrder
  have hb := hBest sample hSample s
  rw [tableAt,FixedArrayTable.read_ofFn,hc] at hb
  obtain ⟨labels,hScore,_,hLabels⟩ := GeneralPaperExactScoreDP.tuple_of_fits scores (costs x w sample) s.val (chosen.atPoint sample) hb.1
  refine ⟨labels,hScore,hLabels,?_⟩
  let a : Affine := ⟨∑ j,anchorQ x j (labels j),∑ j,anchorQ w j (labels j)⟩
  have ha (t : ℚ) : a.value t=∑ j,costs x w t j (labels j) := by
    rw [tuple_affine]
    dsimp only [a,Affine.value]
    ring
  intro t
  rw [←ha t]
  apply GeneralPaperRayClosedAffine.equal_everywhere a chosen.expression lo hi hOrder
  intro u hu
  have hb' := hBest u hu s
  rw [tableAt,FixedArrayTable.read_ofFn,hc] at hb'
  obtain ⟨other,_,hCost,hOther⟩ := GeneralPaperExactScoreDP.tuple_of_fits scores (costs x w u) s.val (chosen.atPoint u) hb'.1
  have he : other=labels := List.ofFn_injective (hOther.trans hLabels.symm)
  subst other
  rw [ha u]
  exact hCost

end Blotto.GeneralPaperRayFixedTuple
