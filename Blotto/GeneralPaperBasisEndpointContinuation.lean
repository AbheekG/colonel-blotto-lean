import Blotto.GeneralPaperBasisThresholdPaths

/-! Actual full original-basis feasibility at the selected classifier
endpoint, for both modification directions. All nonconstant-root bounds
come from the constructed original rows. Endpoint equalities are allowed.
-/
namespace Blotto.GeneralPaperBasisEndpointContinuation
open RationalOrderCell GeneralPaperStrictScore GeneralPaperProxyParameters
open GeneralPaperBasisStoredProducts GeneralPaperBasisState GeneralPaperBasisInvariant
open GeneralPaperBasisSelectedRows GeneralPaperBasisCoordinates GeneralPaperBasisAffineSystem
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem rich {T m : ℕ} (k : ℕ) (hm : 0<m)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (S h N : ℕ) (hN : 0<N) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state)
    (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .rich)
    (hAux : (betaN:ℝ)/(N:ℝ)=((GeneralPaperInitializerSelectedControls.controls m k b false).auxiliary:ℝ)) :
    GeneralPaperAffineConstraintRows.Feasible dict.label (score v S) h
      ((GeneralPaperProxyClassifier.classify m k b).choice.endpoint:ℝ)
      (fun a => value (GeneralPaperBasisAffineData.prepare state)
        ((GeneralPaperProxyClassifier.classify m k b).choice.endpoint:ℝ) (index a)) := by
  have hn : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none := by
    intro he
    rw [hModify] at he
    cases he
  have hs := GeneralPaperBasisAuxiliaryContinuation.to_proxy k hm dict v S h N hN betaN initialGrid state inv b hb false hn hAux
  have hBeta := GeneralPaperBasisContinuationControls.beta_real m k b false
  simp only [Bool.false_eq_true,ite_false] at hBeta
  rw [hBeta] at hs
  have hd := GeneralPaperProxyClassifierPaths.rich_direction m k b hb hModify
  apply GeneralPaperBasisIntervalFeasibility.propagate dict v S h N betaN initialGrid state inv _ _
    (hd.1.trans hd.2).le hs
  intro extra hB gamma hGamma
  have hc := GeneralPaperTransferResidualCoefficients.coefficient_H k hm dict.label (score v S) h
    (selected dict v S h N betaN initialGrid state inv) extra
  exact GeneralPaperBasisThresholdPaths.rich_nonzero m k b hb hModify _ _ hB hc.2.le gamma hGamma

theorem poor {T m : ℕ} (k : ℕ) (hm : 0<m)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (S h N : ℕ) (hN : 0<N) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state)
    (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor)
    (hEndpoint : (0:ℝ)<(GeneralPaperProxyClassifier.classify m k b).choice.endpoint)
    (hAux : (betaN:ℝ)/(N:ℝ)=((GeneralPaperInitializerSelectedControls.controls m k b true).auxiliary:ℝ)) :
    GeneralPaperAffineConstraintRows.Feasible dict.label (score v S) h
      (1/((GeneralPaperProxyClassifier.classify m k b).choice.endpoint:ℝ))
      (fun a => value (GeneralPaperBasisAffineData.prepare state)
        (1/((GeneralPaperProxyClassifier.classify m k b).choice.endpoint:ℝ)) (index a)) := by
  have hn : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none := by
    intro he
    rw [hModify] at he
    cases he
  have hs := GeneralPaperBasisAuxiliaryContinuation.to_proxy k hm dict v S h N hN betaN initialGrid state inv b hb true hn hAux
  have hBeta := GeneralPaperBasisContinuationControls.beta_real m k b true
  simp only [ite_true] at hBeta
  rw [hBeta] at hs
  have hd := GeneralPaperProxyClassifierPaths.poor_reciprocal_direction m k b hb hModify hEndpoint
  apply GeneralPaperBasisIntervalFeasibility.propagate dict v S h N betaN initialGrid state inv _ _
    (hd.1.trans hd.2).le hs
  intro extra hB gamma hGamma
  have hc := GeneralPaperTransferResidualCoefficients.coefficient_H k hm dict.label (score v S) h
    (selected dict v S h N betaN initialGrid state inv) extra
  exact GeneralPaperBasisThresholdPaths.poor_nonzero m k b hb hModify hEndpoint _ _ hB hc.1.le gamma hGamma

end Blotto.GeneralPaperBasisEndpointContinuation
