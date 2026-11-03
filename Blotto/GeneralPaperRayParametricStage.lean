import Blotto.GeneralPaperRayAffineScoreStep

/-! One executed parametric DP stage: compute its pair crossings, narrow
the bracket with on-demand feasibility probes, then retain the affine
minimizers chosen at the new midpoint. This layer is the exact ordinary
score layer throughout the new open bracket.
-/
namespace Blotto.GeneralPaperRayParametricStage
open GeneralPaperRayCrossingRefinement GeneralPaperRayAffineScoreStep
set_option autoImplicit false
set_option maxHeartbeats 3500000

def stage {S K : ℕ} (query : ℚ → Bool × ℕ) (field : Field K) (previous : Table S K) (lo hi : ℚ) :
    Option (Bracket × Table S K) :=
  match narrow query lo hi (crossings field previous) with
  | none => none
  | some b => some (b,step ((b.lower+b.upper)/2) field previous)

theorem layer_best {S K : ℕ} (field : Field K) (previous : Table S K) (lo hi sample t : ℚ)
    (hSample : lo<sample ∧ sample<hi) (ht : lo<t ∧ t<hi)
    (hNoCross : ∀ c∈crossings field previous,¬(lo<c ∧ c<hi))
    (rest : List (GeneralPaperExactScoreDP.Field K))
    (hPrevious : ∀ s,GeneralPaperMinimum.Best (GeneralPaperExactScoreDP.Fits rest s.val) ((tableAt previous t).read s))
    (s : Fin (S+1)) :
    GeneralPaperMinimum.Best (GeneralPaperExactScoreDP.Fits (fieldAt field t::rest) s.val)
      (((step sample field previous).read s).map (fun c => c.atPoint t)) := by
  rw [step_data field previous lo hi sample t hSample ht hNoCross s]
  exact GeneralPaperExactScoreDP.step_best (fieldAt field t) rest (tableAt previous t) hPrevious s

theorem stage_sound {S K : ℕ} (query : ℚ → Bool × ℕ) (field : Field K) (previous : Table S K)
    (lo hi : ℚ) (hOrder : lo<hi) (hLower : (query lo).1=true) (hUpper : (query hi).1=false)
    (hDown : ∀ s t,lo≤s → s≤t → t≤hi → (query t).1=true → (query s).1=true) :
    ∃ b,stage query field previous lo hi=some (b,step ((b.lower+b.upper)/2) field previous) ∧
      Sound query lo hi (crossings field previous) b ∧
      ∀ t,b.lower<t ∧ t<b.upper → ∀ s,
        ((step ((b.lower+b.upper)/2) field previous).read s).map (fun c => c.atPoint t)=
          (GeneralPaperExactScoreDP.step (fieldAt field t) (tableAt previous t)).read s := by
  obtain ⟨b,hRun,hSound⟩ := narrow_sound query lo hi hOrder (crossings field previous) hLower hUpper hDown
  refine ⟨b,by simp only [stage,hRun],hSound,?_⟩
  intro t ht s
  exact step_data field previous b.lower b.upper ((b.lower+b.upper)/2) t
    (GeneralPaperRayStableMinimum.midpoint_inside b.lower b.upper hSound.2.1) ht hSound.2.2.2.2.2 s

end Blotto.GeneralPaperRayParametricStage
