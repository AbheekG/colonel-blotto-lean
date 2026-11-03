import Blotto.GeneralPaperBasisContinuationControls

/-! Actual bounded original residual coefficients preserve feasibility
from the auxiliary vertex through the closed interval to the proxy.
-/
namespace Blotto.GeneralPaperBasisAuxiliaryContinuation
open RationalOrderCell GeneralPaperStrictScore GeneralPaperProxyParameters
open GeneralPaperBasisStoredProducts GeneralPaperBasisState GeneralPaperBasisInvariant
open GeneralPaperBasisSelectedRows GeneralPaperBasisCoordinates GeneralPaperBasisAffineSystem
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem to_proxy {T m : ℕ} (k : ℕ) (hm : 0<m)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (S h N : ℕ) (hN : 0<N) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hAux : (betaN:ℝ)/(N:ℝ)=((GeneralPaperInitializerSelectedControls.controls m k b reciprocal).auxiliary:ℝ)) :
    GeneralPaperAffineConstraintRows.Feasible dict.label (score v S) h
      ((GeneralPaperInitializerSelectedControls.controls m k b reciprocal).beta:ℝ)
      (fun a => value (GeneralPaperBasisAffineData.prepare state)
        ((GeneralPaperInitializerSelectedControls.controls m k b reciprocal).beta:ℝ) (index a)) := by
  have hs := GeneralPaperBasisAffineOriginal.initial_feasible dict v S h N hN betaN initialGrid state inv
  rw [hAux] at hs
  apply GeneralPaperBasisIntervalFeasibility.propagate dict v S h N betaN initialGrid state inv _ _
    (GeneralPaperBasisContinuationControls.auxiliary_le_beta m k hm b hb reciprocal) hs
  intro extra hB gamma hGamma
  exact GeneralPaperInitializerActualRoots.closed_interval_nonzero k hm dict.label (score v S) h
    (selected dict v S h N betaN initialGrid state inv) extra hB b hb hModify reciprocal gamma ⟨hGamma.1,hGamma.2.le⟩

end Blotto.GeneralPaperBasisAuxiliaryContinuation
