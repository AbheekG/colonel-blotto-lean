import Blotto.GeneralPaperRayAffineScoreInput

/-! Execute every parametric score layer, retaining only the latest affine
minima and refining one crossing batch at a time. The resulting table is
an exact complete-score DP throughout its final open bracket. This does
not yet perform the final high-score budget-crossing/blocker extraction.
-/
namespace Blotto.GeneralPaperRayParametricDP
open GeneralPaperRayCrossingRefinement GeneralPaperRayAffineScoreStep GeneralPaperRayParametricStage
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Output (S K : ℕ) where
  bracket : Bracket
  table : Table S K

def run {K : ℕ} (query : ℚ → Bool × ℕ) (S : ℕ) : List (Field K) → ℚ → ℚ → Option (Output S K)
  | [],lo,hi => some ⟨⟨lo,hi⟩,GeneralPaperRayAffineScoreInput.initial S K⟩
  | field::rest,lo,hi =>
    match run query S rest lo hi with
    | none => none
    | some previous =>
      match stage query field previous.table previous.bracket.lower previous.bracket.upper with
      | none => none
      | some current => some ⟨current.1,current.2⟩

def Sound {S K : ℕ} (query : ℚ → Bool × ℕ) (fields : List (Field K)) (lo hi : ℚ) (out : Output S K) : Prop :=
  lo≤out.bracket.lower ∧ out.bracket.lower<out.bracket.upper ∧ out.bracket.upper≤hi ∧
    (query out.bracket.lower).1=true ∧ (query out.bracket.upper).1=false ∧
      ∀ t,out.bracket.lower<t ∧ t<out.bracket.upper → ∀ s,
        GeneralPaperMinimum.Best (GeneralPaperExactScoreDP.Fits (fields.map (fun field => fieldAt field t)) s.val)
          ((tableAt out.table t).read s)

theorem run_sound {K : ℕ} (query : ℚ → Bool × ℕ) (S : ℕ) (fields : List (Field K))
    (lo hi : ℚ) (hOrder : lo<hi) (hLower : (query lo).1=true) (hUpper : (query hi).1=false)
    (hDown : ∀ s t,lo≤s → s≤t → t≤hi → (query t).1=true → (query s).1=true) :
    ∃ out,run query S fields lo hi=some out ∧ Sound query fields lo hi out := by
  induction fields with
  | nil =>
    refine ⟨⟨⟨lo,hi⟩,GeneralPaperRayAffineScoreInput.initial S K⟩,rfl,le_rfl,hOrder,le_rfl,hLower,hUpper,?_⟩
    intro t _ s
    rw [GeneralPaperRayAffineScoreInput.initial_data]
    exact GeneralPaperExactScoreDP.run_best S [] s
  | cons field rest ih =>
    obtain ⟨previous,hRun,hPrevious⟩ := ih
    obtain ⟨b,hStage,hBracket,hData⟩ := stage_sound query field previous.table previous.bracket.lower previous.bracket.upper
      hPrevious.2.1 hPrevious.2.2.2.1 hPrevious.2.2.2.2.1 (by
        intro s t hs hst ht hTrue
        exact hDown s t (hPrevious.1.trans hs) hst (ht.trans hPrevious.2.2.1) hTrue)
    refine ⟨⟨b,step ((b.lower+b.upper)/2) field previous.table⟩,?_,
      hPrevious.1.trans hBracket.1,hBracket.2.1,hBracket.2.2.1.trans hPrevious.2.2.1,
      hBracket.2.2.2.1,hBracket.2.2.2.2.1,?_⟩
    · simp only [run,hRun,hStage]
    · intro t ht s
      have hInside : previous.bracket.lower<t ∧ t<previous.bracket.upper :=
        ⟨hBracket.1.trans_lt ht.1,ht.2.trans_le hBracket.2.2.1⟩
      rw [tableAt,FixedArrayTable.read_ofFn,hData t ht s]
      exact GeneralPaperExactScoreDP.step_best (fieldAt field t) (rest.map (fun field => fieldAt field t))
        (tableAt previous.table t) (hPrevious.2.2.2.2.2 t hInside) s

end Blotto.GeneralPaperRayParametricDP
