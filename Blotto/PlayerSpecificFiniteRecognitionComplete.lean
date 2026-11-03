import Blotto.PlayerSpecificFiniteRecognition

/-! The actual rational/algebraic search rejects exactly when the paper's
qualifying parameter pair does not exist. No real-root/sign oracle occurs
in its source; the real search is used solely for the completeness proof. -/
namespace Blotto.PlayerSpecificFiniteRecognitionComplete
open PlayerSpecificDensePolynomial PlayerSpecificRationalCells PlayerSpecificAlgebraicCandidates
open PlayerSpecificFiniteRecognition
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem complete {n : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput n) (gamma scale : ℝ)
    (hvalid : PlayerSpecificRecognition.ValidParameters i.valuesA.values i.valuesB.values (i.budget:ℝ) gamma scale) :
    ∃ chosen,run model i=some chosen := by
  obtain ⟨chosen,hchosen⟩:=PlayerSpecificRationalRecognition.complete i gamma scale hvalid
  rw [PlayerSpecificRationalRecognition.data] at hchosen
  have hs:=PlayerSpecificRootSearch.sound (i.budget:ℝ)
    (PlayerSpecificRecognition.intervals i.valuesA.values i.valuesB.values (PlayerSpecificRationalRecognition.ids i))
      chosen.1 chosen.2 hchosen
  have hcell : chosen.1∈(PlayerSpecificRationalIntervals.run i).map castCell := by
    rw [PlayerSpecificRationalIntervals.cast_value]
    exact hs.1
  obtain ⟨c,hc,hcast⟩:=List.mem_map.mp hcell
  have hmember : chosen.2∈PlayerSpecificCellCandidates.candidates (castCell c) (i.budget:ℝ) := by rw [hcast]; exact hs.2.1
  have hpass : PlayerSpecificCellCandidates.Passes (castCell c) (i.budget:ℝ) chosen.2 := by rw [hcast]; exact hs.2.2
  obtain ⟨r,hr⟩:=PlayerSpecificFiniteCellCompleteness.complete model c i.budget i.budget_pos.ne'
    (PlayerSpecificRationalIntervals.cubic_nonzero i c hc) chosen.2 hmember hpass
  exact scan_complete model i.budget (PlayerSpecificRationalIntervals.run i) c r hc hr

theorem rejection_iff {n : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput n) :
    run model i=none ↔ ¬∃ gamma scale,
      PlayerSpecificRecognition.ValidParameters i.valuesA.values i.valuesB.values (i.budget:ℝ) gamma scale := by
  constructor
  · intro hn ⟨gamma,scale,hvalid⟩
    obtain ⟨chosen,hchosen⟩:=complete model i gamma scale hvalid
    rw [hn] at hchosen
    cases hchosen
  · intro hnone
    cases hr : run model i with
    | none => rfl
    | some chosen =>
      have hs:=PlayerSpecificFiniteRecognition.sound model i chosen.1 chosen.2 hr
      obtain ⟨x,hx,_⟩:=hs.1.2.2.2.1
      exact (hnone ⟨x,PlayerSpecificCubic.candidateScale (castCell chosen.1).state.coefficients (i.budget:ℝ) x,
        hs.2 x hx.1 hx.2⟩).elim

end Blotto.PlayerSpecificFiniteRecognitionComplete
