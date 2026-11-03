import Blotto.RealOverlapFormula
import Blotto.RationalSegmentLottery
import Blotto.FourGluingDescriptor

/-! Counted real compilation of the complete four-variable overlap descriptor.
Probe restrictions are explicit and match the actual four-variable input. -/

namespace Blotto.RealOverlapFormula
open OverlapFormulaCode
open scoped BigOperators

noncomputable def descriptor {k h : ℕ} (G : OverlapGluing k h) (B : ℝ)
    (hFirst : G.firstProbe = AffineProbe.coordinate 2)
    (hSecond : G.secondProbe = AffineProbe.reflectedCoordinate G.d 0) : SegmentLottery 4 (k * h) :=
  { weight := fun slot => weight.realValue (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)
    P := fun slot r => (safeP r).realValue (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)
    Q := fun slot r => (safeQ r).realValue (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)
    nonnegative := by intro slot; rw [weight_value G B _ _ hFirst hSecond]; exact G.weight_nonnegative _ _
    mass := by
      simp only [weight_value G B _ _ hFirst hSecond]
      exact (G.descriptor B).mass }

theorem descriptor_eq {k h : ℕ} (G : OverlapGluing k h) (B : ℝ)
    (hFirst : G.firstProbe = AffineProbe.coordinate 2)
    (hSecond : G.secondProbe = AffineProbe.reflectedCoordinate G.d 0) :
    descriptor G B hFirst hSecond = G.descriptor B := by
  apply SegmentLottery.eq_of_fields
  · funext slot; exact weight_value G B _ _ hFirst hSecond
  · funext slot r; exact safeP_value G B _ _ hFirst hSecond r
  · funext slot r; exact safeQ_value G B _ _ hFirst hSecond r

theorem weight_operations {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h) :
    (weight.runReal (environment G B i j)).2 ≤ 128 :=
  (weight.runReal_operations_le _).trans weight_operationBound

theorem safeP_operations {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h) (r : Fin 4) :
    ((safeP r).runReal (environment G B i j)).2 ≤ 256 :=
  ((safeP r).runReal_operations_le _).trans (safeP_operationBound r)

theorem safeQ_operations {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h) (r : Fin 4) :
    ((safeQ r).runReal (environment G B i j)).2 ≤ 256 :=
  ((safeQ r).runReal_operations_le _).trans (safeQ_operationBound r)

noncomputable def descriptorWork {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) : ℕ :=
  (∑ slot : Fin (k * h), (weight.runReal (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)).2) +
    (∑ slot : Fin (k * h), ∑ r : Fin 4, ((safeP r).runReal (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)).2) +
    (∑ slot : Fin (k * h), ∑ r : Fin 4, ((safeQ r).runReal (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)).2)

theorem descriptorWork_bound {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) :
    descriptorWork G B ≤ 2176 * (k * h) := by
  have hw : (∑ slot : Fin (k * h), (weight.runReal (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)).2) ≤ (k * h) * 128 := by
    calc
      _ ≤ ∑ _slot : Fin (k * h), 128 := Finset.sum_le_sum (fun slot _ => weight_operations G B _ _)
      _ = _ := by simp
  have hp : (∑ slot : Fin (k * h), ∑ r : Fin 4, ((safeP r).runReal (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)).2) ≤ (k * h) * (4 * 256) := by
    calc
      _ ≤ ∑ _slot : Fin (k * h), ∑ _r : Fin 4, 256 :=
        Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun r _ => safeP_operations G B _ _ r))
      _ = _ := by simp
  have hq : (∑ slot : Fin (k * h), ∑ r : Fin 4, ((safeQ r).runReal (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)).2) ≤ (k * h) * (4 * 256) := by
    calc
      _ ≤ ∑ _slot : Fin (k * h), ∑ _r : Fin 4, 256 :=
        Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun r _ => safeQ_operations G B _ _ r))
      _ = _ := by simp
  unfold descriptorWork
  omega

end Blotto.RealOverlapFormula
