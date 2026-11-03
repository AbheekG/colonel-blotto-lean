import Blotto.GeneralPaperRayCrossingSize

/-! Sorted crossing reads and both narrowed bracket endpoints are drawn
from the incoming endpoints or current batch. Thus their height does not
grow with the number of binary-search iterations or refinement stages.
-/
namespace Blotto.GeneralPaperRayBracketSize
open GeneralPaperRaySortedCrossings GeneralPaperRayCrossingRefinement
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem read_height (lo hi : ℚ) (points : List ℚ) (s : ℕ)
    (hl : RationalHeight lo s) (hh : RationalHeight hi s) (hp : ∀ c∈points,RationalHeight c s)
    (i : Fin (ordered lo hi points).length) : RationalHeight ((array lo hi points).read i) s := by
  have hm := (ordered_mem lo hi points _).mp (read_mem lo hi points i)
  rcases hm with he|he|⟨hm,_,_⟩
  · rw [he]; exact hl
  · rw [he]; exact hh
  · exact hp _ hm

theorem narrow_height (query : ℚ → Bool × ℕ) (lo hi : ℚ) (points : List ℚ) (s : ℕ)
    (hl : RationalHeight lo s) (hh : RationalHeight hi s) (hp : ∀ c∈points,RationalHeight c s)
    (b : Bracket) (hr : narrow query lo hi points=some b) : RationalHeight b.lower s ∧ RationalHeight b.upper s := by
  dsimp only [narrow] at hr
  split at hr
  · have he := Option.some.inj hr
    rw [←he]
    exact ⟨read_height lo hi points s hl hh hp _,read_height lo hi points s hl hh hp _⟩
  · contradiction

theorem stage_height {S K : ℕ} (query : ℚ → Bool × ℕ) (field : GeneralPaperRayAffineScoreStep.Field K)
    (previous : GeneralPaperRayAffineScoreStep.Table S K) (lo hi : ℚ) (s : ℕ)
    (hl : RationalHeight lo s) (hh : RationalHeight hi s)
    (hp : ∀ c∈GeneralPaperRayAffineScoreStep.crossings field previous,RationalHeight c s)
    (out : Bracket × GeneralPaperRayAffineScoreStep.Table S K)
    (hr : GeneralPaperRayParametricStage.stage query field previous lo hi=some out) :
    RationalHeight out.1.lower s ∧ RationalHeight out.1.upper s ∧
      RationalHeight ((out.1.lower+out.1.upper)/2) (2*s+3) := by
  cases hn : narrow query lo hi (GeneralPaperRayAffineScoreStep.crossings field previous) with
  | none =>
    simp only [GeneralPaperRayParametricStage.stage,hn] at hr
    contradiction
  | some b =>
    have he : (b,GeneralPaperRayAffineScoreStep.step ((b.lower+b.upper)/2) field previous)=out := by
      simpa only [GeneralPaperRayParametricStage.stage,hn,Option.some.injEq] using hr
    rw [←he]
    have hb := narrow_height query lo hi _ s hl hh hp b hn
    exact ⟨hb.1,hb.2,GeneralPaperRayAffineBound.midpoint_height hb.1 hb.2⟩

end Blotto.GeneralPaperRayBracketSize
