import Blotto.GeneralPaperRayAffineBound

/-! Every native parametric DP candidate and selected minimum is a bounded
affine sum with exactly the processed number of predecessor labels. The
bound is independent of all sample points and refinement histories.
-/
namespace Blotto.GeneralPaperRayAffineDPSize
open GeneralPaperRayAffine GeneralPaperRayAffineMinimum GeneralPaperRayAffineScoreStep
set_option autoImplicit false
set_option maxHeartbeats 4500000

def FieldBounded {K : ℕ} (D E X W : ℕ) (field : Field K) : Prop :=
  ∀ l,GeneralPaperRayAffineBound.Bounded D E X W (field.read l).2

def ChoiceBounded {K : ℕ} (D E X W n : ℕ) (c : Choice K) : Prop :=
  GeneralPaperRayAffineBound.Bounded D E (n*X) (n*W) c.expression ∧ c.labels.length=n

def TableBounded {S K : ℕ} (D E X W n : ℕ) (table : Table S K) : Prop :=
  ∀ s c,table.read s=some c → ChoiceBounded D E X W n c

theorem initial (D E X W S K : ℕ) : TableBounded D E X W 0 (GeneralPaperRayAffineScoreInput.initial S K) := by
  intro s c hc
  simp only [GeneralPaperRayAffineScoreInput.initial,FixedArrayTable.read_ofFn] at hc
  split at hc
  · have he : c=⟨⟨0,0⟩,[]⟩ := (Option.some.inj hc).symm
    subst c
    exact ⟨by simpa only [Nat.zero_mul] using GeneralPaperRayAffineBound.zero D E,rfl⟩
  · contradiction

theorem extend {K : ℕ} (D E X W n : ℕ) (label : Fin K) (cost : Affine) (tail : Choice K)
    (hc : GeneralPaperRayAffineBound.Bounded D E X W cost) (ht : ChoiceBounded D E X W n tail) :
    ChoiceBounded D E X W (n+1) (GeneralPaperRayAffineScoreStep.extend label cost tail) := by
  refine ⟨?_,?_⟩
  · have hx : (n+1)*X=X+n*X := by ring
    have hw : (n+1)*W=W+n*W := by ring
    change GeneralPaperRayAffineBound.Bounded D E ((n+1)*X) ((n+1)*W) _
    rw [hx,hw]
    exact GeneralPaperRayAffineBound.add hc ht.1
  · change (label::tail.labels).length=n+1
    rw [List.length_cons,ht.2]

theorem candidate {S K : ℕ} (D E X W n : ℕ) (field : Field K) (previous : Table S K)
    (hf : FieldBounded D E X W field) (hp : TableBounded D E X W n previous)
    (s : Fin (S+1)) (l : Fin K) (c : Choice K) (hc : GeneralPaperRayAffineScoreStep.candidate field previous s l=some c) :
    ChoiceBounded D E X W (n+1) c := by
  dsimp only [GeneralPaperRayAffineScoreStep.candidate] at hc
  split at hc
  · rename_i hs
    cases he : previous.read ⟨s.val-(field.read l).1,by omega⟩ with
    | none =>
      simp only [he,Option.map_none] at hc
      contradiction
    | some tail =>
      have hh : GeneralPaperRayAffineScoreStep.extend l (field.read l).2 tail=c := by
        simpa only [he,Option.map_some,Option.some.injEq] using hc
      rw [←hh]
      exact extend D E X W n l _ tail (hf l) (hp _ tail he)
  · contradiction

theorem step {S K : ℕ} (D E X W n : ℕ) (sample : ℚ) (field : Field K) (previous : Table S K)
    (hf : FieldBounded D E X W field) (hp : TableBounded D E X W n previous) :
    TableBounded D E X W (n+1) (GeneralPaperRayAffineScoreStep.step sample field previous) := by
  intro s c hc
  rw [GeneralPaperRayAffineScoreStep.step,FixedArrayTable.read_ofFn] at hc
  obtain ⟨l,_,hl⟩ := scan_origin sample (GeneralPaperRayAffineScoreStep.candidate field previous s) (List.finRange K) c hc
  exact candidate D E X W n field previous hf hp s l c hl

theorem stage {S K : ℕ} (D E X W n : ℕ) (query : ℚ → Bool × ℕ) (field : Field K) (previous : Table S K)
    (lo hi : ℚ) (hf : FieldBounded D E X W field) (hp : TableBounded D E X W n previous)
    (out : GeneralPaperRayCrossingRefinement.Bracket × Table S K)
    (hr : GeneralPaperRayParametricStage.stage query field previous lo hi=some out) :
    TableBounded D E X W (n+1) out.2 := by
  cases hb : GeneralPaperRayCrossingRefinement.narrow query lo hi (crossings field previous) with
  | none =>
    simp only [GeneralPaperRayParametricStage.stage,hb] at hr
    contradiction
  | some b =>
    have he : (b,GeneralPaperRayAffineScoreStep.step ((b.lower+b.upper)/2) field previous)=out := by
      simpa only [GeneralPaperRayParametricStage.stage,hb,Option.some.injEq] using hr
    rw [←he]
    exact step D E X W n _ field previous hf hp

theorem run {K : ℕ} (D E X W S : ℕ) (query : ℚ → Bool × ℕ) (fields : List (Field K))
    (lo hi : ℚ) (hf : ∀ f∈fields,FieldBounded D E X W f) (out : GeneralPaperRayParametricDP.Output S K)
    (hr : GeneralPaperRayParametricDP.run query S fields lo hi=some out) :
    TableBounded D E X W fields.length out.table := by
  induction fields generalizing lo hi out with
  | nil =>
    have he : (⟨⟨lo,hi⟩,GeneralPaperRayAffineScoreInput.initial S K⟩ : GeneralPaperRayParametricDP.Output S K)=out := by
      simpa only [GeneralPaperRayParametricDP.run,Option.some.injEq] using hr
    rw [←he]
    exact initial D E X W S K
  | cons field rest ih =>
    cases hp : GeneralPaperRayParametricDP.run query S rest lo hi with
    | none =>
      simp only [GeneralPaperRayParametricDP.run,hp] at hr
      contradiction
    | some previous =>
      cases hs : GeneralPaperRayParametricStage.stage query field previous.table previous.bracket.lower previous.bracket.upper with
      | none =>
        simp only [GeneralPaperRayParametricDP.run,hp,hs] at hr
        contradiction
      | some current =>
        have he : (⟨current.1,current.2⟩ : GeneralPaperRayParametricDP.Output S K)=out := by
          simpa only [GeneralPaperRayParametricDP.run,hp,hs,Option.some.injEq] using hr
        rw [←he]
        exact stage D E X W rest.length query field previous.table _ _ (hf field List.mem_cons_self)
          (ih lo hi (fun f hf' => hf f (List.mem_cons_of_mem _ hf')) previous hp) current hs

end Blotto.GeneralPaperRayAffineDPSize
