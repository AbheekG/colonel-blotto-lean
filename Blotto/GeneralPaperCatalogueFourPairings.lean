import Blotto.GeneralPaperCatalogueFiniteLosses

/-! Actual loss pairings at a global source iteration. Their exact
cancellation uses the executed p,q,lambda,mu, the actual selected whole
rows, and arbitrary fixed comparator marginals/multipliers. These are the
pairings entering the already-checked global regret, after exact reindexing.
-/
namespace Blotto.GeneralPaperCatalogueFourPairings
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCodeCDF GeneralPaperSignedPairing GeneralPaperFourLossAlgebra
open GeneralPaperCatalogueFiniteFamilies GeneralPaperCatalogueFiniteLosses
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem resize_regret {n p : ℕ} (h : n=p) (f loss : Fin n → ℝ) (u : Fin p → ℝ) :
    dot (fun i => resize h f i-u i) (resize h loss)=
      dot (fun i => f i-resize h.symm u i) loss := by
  cases h
  rfl

noncomputable def pairings {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) (x y : Fin (2^a.lambda) → ℝ)
    (testLambda testMu : Fin (2^a.lambda+2^a.lambda) → ℝ) : ℝ :=
  dot (fun i => unsigned false a k Qv weights Bc Br time j i-x i) (unsignedTruth false a k Qv weights Bc Br time j)+
    dot (fun i => unsigned true a k Qv weights Bc Br time j i-y i) (unsignedTruth true a k Qv weights Bc Br time j)+
    dot (fun i => signedFamily false a k Qv weights Bc Br time j i-testLambda i) (signedTruth false a k Qv weights Bc Br time j)+
    dot (fun i => signedFamily true a k Qv weights Bc Br time j i-testMu i) (signedTruth true a k Qv weights Bc Br time j)

theorem pairings_eq {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (ht : time<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (j : Fin m)
    (x y : Fin (2^a.lambda) → ℝ) (testLambda testMu : Fin (2^a.lambda+2^a.lambda) → ℝ) :
    pairings a k Qv weights Bc Br time j x y testLambda testMu=
      fieldRegret (unsigned false a k Qv weights Bc Br time j) (unsigned true a k Qv weights Bc Br time j) x y
        (signedFamily false a k Qv weights Bc Br time j) (signedFamily true a k Qv weights Bc Br time j)
        testLambda testMu (row false a k Qv weights Bc Br time j) (row true a k Qv weights Bc Br time j) := by
  have hp := funext (p_loss a k Qv weights Bc Br time ht j)
  have hq := funext (q_loss a k Qv weights Bc Br time ht j)
  have hl := funext (signed_loss false a k Qv weights Bc Br time ht j)
  have hm := funext (signed_loss true a k Qv weights Bc Br time ht j)
  unfold pairings fieldRegret
  rw [hp,hq,hl,hm]

theorem cancellation {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (ht : time<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (j : Fin m)
    (x y : Fin (2^a.lambda) → ℝ) (testLambda testMu : Fin (2^a.lambda+2^a.lambda) → ℝ) :
    pairings a k Qv weights Bc Br time j x y testLambda testMu=
      codePayoff (unsigned false a k Qv weights Bc Br time j) y-codePayoff x (unsigned true a k Qv weights Bc Br time j)+
        pair testLambda (fun i => cdf (unsigned false a k Qv weights Bc Br time j) i-rowCDF (row false a k Qv weights Bc Br time j) i)+
        pair testMu (fun i => cdf (unsigned true a k Qv weights Bc Br time j) i-rowCDF (row true a k Qv weights Bc Br time j) i)+
        (tail (signedFamily false a k Qv weights Bc Br time j) (row false a k Qv weights Bc Br time j).val-
          pair (signedFamily false a k Qv weights Bc Br time j) (cdf x))+
        (tail (signedFamily true a k Qv weights Bc Br time j) (row true a k Qv weights Bc Br time j).val-
          pair (signedFamily true a k Qv weights Bc Br time j) (cdf y)) := by
  rw [pairings_eq a k Qv weights Bc Br time ht j x y testLambda testMu]
  exact GeneralPaperFourLossAlgebra.cancellation _ _ _ _ _ _ _ _ _ _
    (unsigned_probability true a k Qv weights Bc Br time j).2

end Blotto.GeneralPaperCatalogueFourPairings
