import Blotto.GeneralPaperRayBlockerRows

/-! Complete paper ray-endpoint program. Scan original static rows once;
accept their endpoint if the full-score predicate passes, otherwise run
all parametric score layers, the final budget batch and fixed predecessor
recovery. The prepared entry reuses one score matrix across all phases.
-/
namespace Blotto.GeneralPaperRayEndpoint
open RationalOrderCell GeneralPaperRayBlockerRows
set_option autoImplicit false

structure Answer (T m K : ℕ) where
  time : ℚ
  blocker : Descriptor T m K

def prepared {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ) (beta : ℚ)
    (x w : Variable m K → ℚ) : Option (Answer T m K) :=
  let static := GeneralPaperStaticRayScan.scan labels x w
  match static.choice with
  | none => none
  | some c =>
    if (GeneralPaperRayPricedPredicate.query matrix x w S h beta c.time).1=true then
      some ⟨c.time,.inl c.blocker⟩
    else
      (GeneralPaperRayHighSearch.prepared matrix S h beta x w 0 c.time).map (fun high => ⟨high.time,.inr high.labels⟩)

def execute {T m K : ℕ} (scoreDepth : ℕ) (d : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h : ℕ) (beta : ℚ) (x w : Variable m K → ℚ) : Option (Answer T m K) :=
  prepared d.label (GeneralPaperScoreMatrixWork.matrixRun scoreDepth d v S).1 S h beta x w

end Blotto.GeneralPaperRayEndpoint
