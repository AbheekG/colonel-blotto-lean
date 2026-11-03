import Blotto.GeneralPaperParametricStageWork

/-! Returned crossing brackets stay in the incoming bracket regardless of
query truth or monotonicity. These are execution invariants, not feasibility
certificates, and therefore also support prices on every failure path.
-/
namespace Blotto.GeneralPaperRayBracketContainment
open GeneralPaperRayCrossingRefinement GeneralPaperRaySortedCrossings
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem narrow (query : ℚ → Bool × ℕ) (lo hi : ℚ) (points : List ℚ) (hOrder : lo≤hi)
    (b : Bracket) (hr : GeneralPaperRayCrossingRefinement.narrow query lo hi points=some b) :
    lo≤b.lower ∧ b.lower≤b.upper ∧ b.upper≤hi := by
  dsimp only [GeneralPaperRayCrossingRefinement.narrow] at hr
  split at hr
  · rename_i hRank
    have he := Option.some.inj hr
    rw [←he]
    let values := array lo hi points
    let rank := (GeneralPaperRaySearchControls.selected (fun i => query (values.read i))).rank
    change 0<rank ∧ rank<(ordered lo hi points).length at hRank
    let left : Fin (ordered lo hi points).length := ⟨rank-1,by omega⟩
    let right : Fin (ordered lo hi points).length := ⟨rank,hRank.2⟩
    have hL := ordered_bound lo hi hOrder points (values.read left) (read_mem lo hi points left)
    have hU := ordered_bound lo hi hOrder points (values.read right) (read_mem lo hi points right)
    refine ⟨hL.1,?_,hU.2⟩
    exact (read_strict lo hi points).monotone (show left≤right by change rank-1≤rank; omega)
  · contradiction

theorem stage {S K : ℕ} (query : ℚ → Bool × ℕ) (field : GeneralPaperRayAffineScoreStep.Field K)
    (previous : GeneralPaperRayAffineScoreStep.Table S K) (lo hi : ℚ) (hOrder : lo≤hi)
    (out : Bracket × GeneralPaperRayAffineScoreStep.Table S K)
    (hr : GeneralPaperRayParametricStage.stage query field previous lo hi=some out) :
    lo≤out.1.lower ∧ out.1.lower≤out.1.upper ∧ out.1.upper≤hi := by
  cases hn : GeneralPaperRayCrossingRefinement.narrow query lo hi
      (GeneralPaperRayAffineScoreStep.crossings field previous) with
  | none => simp only [GeneralPaperRayParametricStage.stage,hn] at hr; contradiction
  | some b =>
    have he : (b,GeneralPaperRayAffineScoreStep.step ((b.lower+b.upper)/2) field previous)=out := by
      simpa only [GeneralPaperRayParametricStage.stage,hn,Option.some.injEq] using hr
    rw [←he]
    exact narrow query lo hi _ hOrder b hn

theorem run {S K : ℕ} (query : ℚ → Bool × ℕ) (fields : List (GeneralPaperRayAffineScoreStep.Field K))
    (lo hi : ℚ) (hOrder : lo≤hi) (out : GeneralPaperRayParametricDP.Output S K)
    (hr : GeneralPaperRayParametricDP.run query S fields lo hi=some out) :
    lo≤out.bracket.lower ∧ out.bracket.lower≤out.bracket.upper ∧ out.bracket.upper≤hi := by
  induction fields generalizing out with
  | nil =>
    have he : (⟨⟨lo,hi⟩,GeneralPaperRayAffineScoreInput.initial S K⟩ : GeneralPaperRayParametricDP.Output S K)=out := by
      simpa only [GeneralPaperRayParametricDP.run,Option.some.injEq] using hr
    rw [←he]
    exact ⟨le_rfl,hOrder,le_rfl⟩
  | cons field rest ih =>
    cases hp : GeneralPaperRayParametricDP.run query S rest lo hi with
    | none => simp only [GeneralPaperRayParametricDP.run,hp] at hr; contradiction
    | some previous =>
      have hPrevious := ih previous hp
      cases hs : GeneralPaperRayParametricStage.stage query field previous.table previous.bracket.lower previous.bracket.upper with
      | none => simp only [GeneralPaperRayParametricDP.run,hp,hs] at hr; contradiction
      | some current =>
        have he : (⟨current.1,current.2⟩ : GeneralPaperRayParametricDP.Output S K)=out := by
          simpa only [GeneralPaperRayParametricDP.run,hp,hs,Option.some.injEq] using hr
        rw [←he]
        have hc := stage query field previous.table _ _ hPrevious.2.1 current hs
        exact ⟨hPrevious.1.trans hc.1,hc.2.1,hc.2.2.trans hPrevious.2.2⟩

end Blotto.GeneralPaperRayBracketContainment
