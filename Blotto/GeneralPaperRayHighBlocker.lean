import Blotto.GeneralPaperRayBlockerAlgebra

/-! Extract an original high tuple from the retained affine predecessors.
Its constraint is tight at the feasible left endpoint with positive slope,
and it is strictly violated at every later rational parameter.
-/
namespace Blotto.GeneralPaperRayHighBlocker
open RationalOrderCell GeneralPaperStrictScore GeneralPaperRayAffineMinimum GeneralPaperRayAffineScoreStep
open GeneralPaperRayAnchorCosts GeneralPaperRayFeasibility GeneralPaperRayTableFeasibility GeneralPaperRayBudgetCrossings
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

def extract {S K : ℕ} (m : ℕ) (table : Table S K) (h : ℕ) (beta lo hi : ℚ) : Option (FixedArrayTable m (Fin K)) :=
  (GeneralPaperRayFixedViolation.run table h beta ((lo+hi)/2)).value.bind (fun entry => GeneralPaperRayFixedTuple.decode m entry.2)

theorem extract_sound {m S K : ℕ} (v : RationalFieldSelector m) (hK : 0<K) (x w : Variable m K → ℚ)
    (table : Table S K) (h : ℕ) (beta lo hi : ℚ) (hOrder : lo<hi)
    (hLower : test v S h beta x w lo=true) (hMiddle : test v S h beta x w ((lo+hi)/2)=false)
    (hBest : ∀ t,lo<t ∧ t<hi → ∀ s,GeneralPaperMinimum.Best (GeneralPaperExactScoreDP.Fits
      (GeneralPaperExactScoreDP.fields (score v S) (costs x w t)) s.val) ((tableAt table t).read s))
    (hNoCross : ∀ r∈batch table h beta,¬(lo<r ∧ r<hi)) :
    ∃ row,extract m table h beta lo hi=some row ∧ h<(∑ j,score v S j (row.read j)) ∧
      (GeneralPaperRayTupleResidual.residual x w beta row.read).value lo=0 ∧
        0<(GeneralPaperRayTupleResidual.residual x w beta row.read).slope ∧
          ∀ t,lo<t → 0<(GeneralPaperRayTupleResidual.residual x w beta row.read).value t := by
  let sample := (lo+hi)/2
  have hSample := GeneralPaperRayStableMinimum.midpoint_inside lo hi hOrder
  have hNot : ¬TableFeasible table h beta sample := by
    intro hGood
    have ht := (test_iff v hK x w table h beta sample (hBest sample hSample)).mpr hGood
    rw [hMiddle] at ht
    contradiction
  obtain ⟨entry,hEntry⟩ := GeneralPaperRayFixedViolation.run_exists table h beta sample hNot
  have hValid := GeneralPaperRayFixedViolation.scan_valid table h beta sample (List.finRange (S+1)) entry hEntry
  obtain ⟨labels,hScore,hLabels,hTuple⟩ := GeneralPaperRayFixedTuple.tuple_everywhere (score v S) x w table lo hi hOrder
    entry.1 entry.2 hValid.2.1 hBest
  have hHigh : h<(∑ j,score v S j (labels j)) := by rw [hScore]; exact hValid.1
  have hLowerCost : beta≤entry.2.expression.value lo := by
    have hf := (GeneralPaperRayHighSound.passes_iff (score v S) (costs x w lo) S h
      (fun labels => GeneralPaperComputedThreshold.totalScore_le v S hK labels) beta).mp hLower
    have hh := hf labels hHigh
    rwa [hTuple lo] at hh
  have hBlock := GeneralPaperRayBlockerAlgebra.positive_blocker (comparison beta entry.2) lo hi sample hSample
    ((comparison_iff beta entry.2 lo).mpr hLowerCost)
    (by rw [comparison_value]; exact sub_pos.mpr hValid.2.2)
    (fun hp => hNoCross _ (batch_complete table h beta entry.1 hValid.1 entry.2 hValid.2.1 hp))
  have hValue (t : ℚ) : (GeneralPaperRayTupleResidual.residual x w beta labels).value t=(comparison beta entry.2).value t := by
    rw [GeneralPaperRayTupleResidual.residual_value,comparison_value,hTuple t]
  have hSlope := GeneralPaperRayBlockerAlgebra.slope_equal (GeneralPaperRayTupleResidual.residual x w beta labels) (comparison beta entry.2) hValue
  obtain ⟨row,hDecode,hRead⟩ := GeneralPaperRayFixedTuple.decode_labels entry.2 labels hLabels
  refine ⟨row,?_,by rw [hRead]; exact hHigh,?_,?_,?_⟩
  · change ((GeneralPaperRayFixedViolation.run table h beta sample).value.bind
      (fun entry => GeneralPaperRayFixedTuple.decode m entry.2))=some row
    rw [hEntry]
    exact hDecode
  · rw [hRead,hValue]
    exact hBlock.2.1
  · rw [hRead,hSlope]
    exact hBlock.1
  · intro t ht
    rw [hRead,hValue]
    exact hBlock.2.2 t ht

end Blotto.GeneralPaperRayHighBlocker
