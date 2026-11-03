import Blotto.RationalOverlapFormula
import Blotto.RationalThreeGeometryCompiler


/-! Counted rational compilation of the complete four-variable overlap descriptor.
Both runtimes use the same expression description. -/

namespace Blotto.RationalOverlapFormula
open OverlapFormulaCode
open scoped BigOperators

def descriptorReference {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) : RationalSegmentLottery 4 (k * h) :=
  { weight := fun slot => weight.value (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)
    P := fun slot r => (safeP r).value (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)
    Q := fun slot r => (safeQ r).value (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)
    nonnegative := by intro slot; rw [weight_value G B _ _]; exact G.weight_nonnegative _ _
    mass := by
      simp only [weight_value G B _ _]
      exact (G.descriptor B).mass }

def descriptor {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) : RationalSegmentLottery 4 (k * h) :=
  (PreparedSegmentDescriptor.prepare (descriptorReference G B)).lottery

theorem descriptor_eq {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) :
    descriptor G B = G.descriptor B := by
  rw [descriptor, PreparedSegmentDescriptor.lottery_eq]
  apply RationalSegmentLottery.eq_of_fields
  · funext slot; exact weight_value G B _ _
  · funext slot r; exact safeP_value G B _ _ r
  · funext slot r; exact safeQ_value G B _ _ r

theorem weight_operations {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) :
    (weight.run (environment G B i j)).2 ≤ 128 :=
  (weight.run_operations_le _).trans weight_operationBound

theorem safeP_operations {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) (r : Fin 4) :
    ((safeP r).run (environment G B i j)).2 ≤ 256 :=
  ((safeP r).run_operations_le _).trans (safeP_operationBound r)

theorem safeQ_operations {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) (i : Fin k) (j : Fin h) (r : Fin 4) :
    ((safeQ r).run (environment G B i j)).2 ≤ 256 :=
  ((safeQ r).run_operations_le _).trans (safeQ_operationBound r)

def descriptorWork {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) : ℕ :=
  (∑ slot : Fin (k * h), (weight.run (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)).2) +
    (∑ slot : Fin (k * h), ∑ r : Fin 4, ((safeP r).run (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)).2) +
    (∑ slot : Fin (k * h), ∑ r : Fin 4, ((safeQ r).run (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)).2)

theorem descriptorWork_bound {k h : ℕ} (G : RationalOverlapGluing k h) (B : ℚ) :
    descriptorWork G B ≤ 2176 * (k * h) := by
  have hw : (∑ slot : Fin (k * h), (weight.run (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)).2) ≤ (k * h) * 128 := by
    calc
      _ ≤ ∑ _slot : Fin (k * h), 128 := Finset.sum_le_sum (fun slot _ => weight_operations G B _ _)
      _ = _ := by simp
  have hp : (∑ slot : Fin (k * h), ∑ r : Fin 4, ((safeP r).run (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)).2) ≤ (k * h) * (4 * 256) := by
    calc
      _ ≤ ∑ _slot : Fin (k * h), ∑ _r : Fin 4, 256 :=
        Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun r _ => safeP_operations G B _ _ r))
      _ = _ := by simp
  have hq : (∑ slot : Fin (k * h), ∑ r : Fin 4, ((safeQ r).run (environment G B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)).2) ≤ (k * h) * (4 * 256) := by
    calc
      _ ≤ ∑ _slot : Fin (k * h), ∑ _r : Fin 4, 256 :=
        Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun r _ => safeQ_operations G B _ _ r))
      _ = _ := by simp
  unfold descriptorWork
  omega

end Blotto.RationalOverlapFormula
