import Blotto.GeneralPaperRayUniformSize

/-! Uniform rational heights throughout the ACTUAL complete parametric
DP recursion. Each new batch is bounded from its affine sums; incoming
bracket endpoints are retained rather than recomputed from old midpoints.
-/
namespace Blotto.GeneralPaperRayParametricRunSize
open GeneralPaperRayUniformSize GeneralPaperRayAffineScoreStep
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem bracket {K D E X W P m S : ℕ} (hD : 0<D) (hE : 0<E) (query : ℚ → Bool × ℕ)
    (fields : List (Field K)) (lo hi : ℚ) (hLen : fields.length≤m)
    (hf : ∀ f∈fields,GeneralPaperRayAffineDPSize.FieldBounded D E X W f)
    (hl : RationalHeight lo (width D E m X W P)) (hh : RationalHeight hi (width D E m X W P))
    (out : GeneralPaperRayParametricDP.Output S K) (hr : GeneralPaperRayParametricDP.run query S fields lo hi=some out) :
    RationalHeight out.bracket.lower (width D E m X W P) ∧ RationalHeight out.bracket.upper (width D E m X W P) := by
  induction fields generalizing lo hi out with
  | nil =>
    have he : (⟨⟨lo,hi⟩,GeneralPaperRayAffineScoreInput.initial S K⟩ : GeneralPaperRayParametricDP.Output S K)=out := by
      simpa only [GeneralPaperRayParametricDP.run,Option.some.injEq] using hr
    rw [←he]
    exact ⟨hl,hh⟩
  | cons field rest ih =>
    cases hp : GeneralPaperRayParametricDP.run query S rest lo hi with
    | none =>
      simp only [GeneralPaperRayParametricDP.run,hp] at hr
      contradiction
    | some previous =>
      have hRestLen : rest.length≤m := by simp only [List.length_cons] at hLen; omega
      have hRest := ih lo hi hRestLen (fun f h => hf f (List.mem_cons_of_mem _ h)) hl hh previous hp
      have hTable := GeneralPaperRayAffineDPSize.run D E X W S query rest lo hi
        (fun f h => hf f (List.mem_cons_of_mem _ h)) previous hp
      cases hs : GeneralPaperRayParametricStage.stage query field previous.table previous.bracket.lower previous.bracket.upper with
      | none =>
        simp only [GeneralPaperRayParametricDP.run,hp,hs] at hr
        contradiction
      | some current =>
        have he : (⟨current.1,current.2⟩ : GeneralPaperRayParametricDP.Output S K)=out := by
          simpa only [GeneralPaperRayParametricDP.run,hp,hs,Option.some.injEq] using hr
        rw [←he]
        have hn : rest.length+1≤m := hLen
        have hRoots := stage_roots (P:=P) hD hE hn field previous.table (hf field List.mem_cons_self) hTable
        have hStage := GeneralPaperRayBracketSize.stage_height query field previous.table _ _ _ hRest.1 hRest.2 hRoots current hs
        exact ⟨hStage.1,hStage.2.1⟩

theorem finish {S K D E X W P m n : ℕ} (hD : 0<D) (hE : 0<E) (hn : n≤m)
    (query : ℚ → Bool × ℕ) (table : Table S K) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X W n table)
    (h : ℕ) (beta lo hi : ℚ) (hb : GeneralPaperRayRationalBound.Bounded D P beta)
    (hl : RationalHeight lo (width D E m X W P)) (hh : RationalHeight hi (width D E m X W P))
    (out : GeneralPaperRayCrossingRefinement.Bracket)
    (hr : GeneralPaperRayCrossingRefinement.narrow query lo hi (GeneralPaperRayBudgetCrossings.batch table h beta)=some out) :
    RationalHeight out.lower (width D E m X W P) ∧ RationalHeight out.upper (width D E m X W P) ∧
      RationalHeight ((out.lower+out.upper)/2) (2*width D E m X W P+3) := by
  have hRoots := budget_roots hD hE hn table hp h beta hb
  have hs := GeneralPaperRayBracketSize.narrow_height query lo hi _ _ hl hh hRoots out hr
  exact ⟨hs.1,hs.2,GeneralPaperRayAffineBound.midpoint_height hs.1 hs.2⟩

end Blotto.GeneralPaperRayParametricRunSize
