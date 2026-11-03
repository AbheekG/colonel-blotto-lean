import Blotto.GeneralPaperRayHighBlocker

/-! Complete executed high-tuple ray-endpoint search after a rejected
static endpoint. All parametric score layers, the final budget batch and
fixed-predecessor extraction run on the actual normalized score data.
-/
namespace Blotto.GeneralPaperRayHighSearch
open RationalOrderCell GeneralPaperStrictScore GeneralPaperRayFeasibility GeneralPaperRayAffineScoreStep
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Answer (m K : ℕ) where
  time : ℚ
  labels : FixedArrayTable m (Fin K)

def prepared {m K : ℕ} (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (S h : ℕ) (beta : ℚ) (x w : Variable m K → ℚ) (lo hi : ℚ) : Option (Answer m K) :=
  match GeneralPaperRayParametricDP.run (GeneralPaperRayPricedPredicate.query matrix x w S h beta) S
      (GeneralPaperRayAffineScoreInput.fields matrix x w) lo hi with
  | none => none
  | some out =>
    match GeneralPaperRayFinalBudget.finish matrix out.table x w h beta out.bracket.lower out.bracket.upper with
    | none => none
    | some b =>
      match GeneralPaperRayHighBlocker.extract m out.table h beta b.lower b.upper with
      | none => none
      | some row => some ⟨b.lower,row⟩

def search {T m K : ℕ} (scoreDepth : ℕ) (d : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h : ℕ) (beta : ℚ) (x w : Variable m K → ℚ) (lo hi : ℚ) : Option (Answer m K) :=
  prepared (GeneralPaperScoreMatrixWork.matrixRun scoreDepth d v S).1 S h beta x w lo hi

theorem search_sound {T m S K : ℕ} (scoreDepth : ℕ) (d : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (hK : 0<K) (hCap : S<2^scoreDepth) (x w : Variable m K → ℚ)
    (h : ℕ) (beta lo hi : ℚ) (hLo : 0≤lo) (hOrder : lo<hi)
    (hStart : test v S h beta x w 0=true) (hLower : test v S h beta x w lo=true) (hUpper : test v S h beta x w hi=false) :
    ∃ answer,search scoreDepth d v S h beta x w lo hi=some answer ∧
      lo≤answer.time ∧ answer.time<hi ∧ test v S h beta x w answer.time=true ∧
        h<(∑ j,score v S j (answer.labels.read j)) ∧
          (GeneralPaperRayTupleResidual.residual x w beta answer.labels.read).value answer.time=0 ∧
            0<(GeneralPaperRayTupleResidual.residual x w beta answer.labels.read).slope ∧
              ∀ t,answer.time<t → 0<(GeneralPaperRayTupleResidual.residual x w beta answer.labels.read).value t := by
  obtain ⟨out,hDP,hOutL,hOutOrder,hOutU,hOutTrue,hOutFalse,hBest⟩ :=
    GeneralPaperRayActualParametricDP.actual_sound scoreDepth d v hK S h hCap beta x w hStart lo hi hLo hOrder hLower hUpper
  obtain ⟨b,hFinal,hL,hOrder',hU,hTrue,_,hNoCross,hOpenFalse⟩ := GeneralPaperRayFinalBudget.actual_sound
    scoreDepth d v hK hCap x w out.table h beta out.bracket.lower out.bracket.upper (hLo.trans hOutL)
    hOutOrder hStart hOutTrue hOutFalse hBest
  have hNewBest (t : ℚ) (ht : b.lower<t ∧ t<b.upper) := hBest t ⟨hL.trans_lt ht.1,ht.2.trans_le hU⟩
  obtain ⟨row,hExtract,hHigh,hTight,hSlope,hBeyond⟩ := GeneralPaperRayHighBlocker.extract_sound v hK x w out.table h beta
    b.lower b.upper hOrder' hTrue (hOpenFalse _ (GeneralPaperRayStableMinimum.midpoint_inside _ _ hOrder')) hNewBest hNoCross
  refine ⟨⟨b.lower,row⟩,?_,hOutL.trans hL,hOrder'.trans_le (hU.trans hOutU),hTrue,hHigh,hTight,hSlope,hBeyond⟩
  simp only [GeneralPaperRayActualParametricDP.execute] at hDP
  simp only [search,prepared,hDP,hFinal,hExtract]

end Blotto.GeneralPaperRayHighSearch
