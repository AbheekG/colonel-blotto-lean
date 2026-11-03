import Blotto.GeneralPaperSourceRayOperandSize

/-! The affine evaluations compared by native minimum selection and the
two operands of each complete-score budget predicate have uniform heights.
This is an operand theorem; pricing the full primitive execution and
simultaneous storage remains a separate required join.
-/
namespace Blotto.GeneralPaperRayComparisonOperandSize
open RationalOrderCell GeneralPaperRayUniformSize GeneralPaperRayRationalBound
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem affine_value {D E m X W P : ℕ} (hD : 0<D) (hE : 0<E)
    (f : GeneralPaperRayAffine.Affine)
    (hf : GeneralPaperRayAffineBound.Bounded D E (interceptCap m X P) (slopeCap m W) f)
    (t : ℚ) (ht : RationalHeight t (2*width D E m X W P+3)) :
    RationalHeight (f.value t) (3*width D E m X W P+4) := by
  have hh := GeneralPaperRayAffineBound.value_height hD hE hf t ht
  have hc := GeneralPaperRayAffineBound.rootWidth_mono D E (interceptCap m X P) (slopeCap m W)
    (interceptCap m X P+interceptCap m X P) (slopeCap m W+slopeCap m W) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  change binaryWordWidth (interceptCap m X P+1)+binaryWordWidth D+
    binaryWordWidth (slopeCap m W+1)+binaryWordWidth E≤width D E m X W P at hc
  exact hh.mono (by omega)

theorem predicate {m K D E X W P s : ℕ} (hD : 0<D) (hED : E∣D)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E W (w a))
    (beta : ℚ) (hb : Bounded D P beta) (t : ℚ) (ht : 0≤t ∧ t≤1) (hT : RationalHeight t s)
    (S h : ℕ) (c : GeneralPaperMinimum.Selection K)
    (hc : (GeneralPaperRayQueryWork.minimumRun matrix x w t S h).1=some c) :
    RationalHeight beta (width D E m X W P+s) ∧ RationalHeight c.cost (width D E m X W P+s) := by
  have hBase := GeneralPaperRayFixedQuerySize.predicate_heights D E X W P hD hED matrix x w hx hw beta hb t ht S h c hc
  let A := interceptCap m X P
  let B := slopeCap m W
  have hCap : P+m*(X+W)+1≤A+1+B := by unfold A B interceptCap slopeCap; nlinarith
  have hM := binaryWordWidth_mono hCap
  have hSum := GeneralPaperRayOperandWidthEnvelope.word_add (A+1) B
  have hA := binaryWordWidth_mono (show A+1≤A+A+1 by omega)
  have hB := binaryWordWidth_mono (show B≤B+B+1 by omega)
  have hE := binaryWordWidth_pos E
  have hPeriod := binaryWordWidth_mul D t.den
  have hDen := binaryWordWidth_le_of_lt_pow hT.positive hT.2
  have hWidth : binaryWordWidth (P+m*(X+W)+1)+binaryWordWidth (D*t.den)≤width D E m X W P+s := by
    change _≤binaryWordWidth (A+A+1)+binaryWordWidth D+binaryWordWidth (B+B+1)+binaryWordWidth E+s
    omega
  exact ⟨hBase.1.mono hWidth,hBase.2.mono hWidth⟩

end Blotto.GeneralPaperRayComparisonOperandSize
