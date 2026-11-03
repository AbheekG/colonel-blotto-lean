import Blotto.GeneralPaperSourceModifiedCompilerBitPrice
import Blotto.GeneralPaperRetainedCompilerPairBits

/-! The whole selected compiler pair has a complete local bit profile.
It charges native endpoint metadata and the one reached modified side;
the sum of two possible side profiles is an erased worst-case majorant. -/
namespace Blotto.GeneralPaperSourceCompilerPairBitPrice
open GeneralPaperProxyParameters GeneralPaperOriginalDrawEquilibrium
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def metadataProfile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  64*W+2*model.rat (1+binaryWordWidth ((prepare m k).Qg+1))

theorem metadata_work (model : RationalCostModel) (W m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) :
    (GeneralPaperRetainedEndpointFraction.run model.rat W (prepare m k).Qg (grid_positive m k)
      (GeneralPaperProxyClassifier.classify m k b)).2≤metadataProfile model W m k := by
  have hCell : (GeneralPaperProxyClassifier.classify m k b).cell<(prepare m k).Qg :=
    (GeneralPaperProxyQuotient.locate_spec m k b hb).1
  have hAdd := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b)
    (GeneralPaperProxyClassifier.classify m k b).cell 1 ((prepare m k).Qg+1) (by omega) (by omega) (by omega)
  unfold GeneralPaperRetainedEndpointFraction.run
  split
  · unfold metadataProfile; omega
  · cases hr : (GeneralPaperProxyClassifier.classify m k b).root with
    | none => dsimp only; split <;> dsimp only <;> unfold metadataProfile <;> omega
    | some f => dsimp only; unfold metadataProfile; omega

def profile (model : RationalCostModel) (W m k Qv p q : ℕ) : ℕ :=
  GeneralPaperSourceModifiedCompilerBitPrice.columnProfile model W m k Qv p q false+
  GeneralPaperSourceModifiedCompilerBitPrice.columnProfile model W m k Qv p q true+
  metadataProfile model W m k+64*W

theorem actual_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1)
    (columns : Columns (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K)
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hRich : GeneralPaperRowQuantizer.dictionary columns.rich=GeneralPaperSourceUnchangedDictionary.run k Qv weights b false)
    (hPoor : GeneralPaperRowQuantizer.dictionary columns.poor=GeneralPaperSourceUnchangedDictionary.run k Qv weights b true)
    (hValues : GeneralPaperRetainedFieldValues.selector values=GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
    (hW : 1≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth ((prepare m k).S+4)≤W) (hColumnsIndex : binaryWordWidth (m+(prepare m k).K+1)≤W) :
    let classified := GeneralPaperProxyClassifier.classify m k b
    (GeneralPaperRetainedCompilerPairBits.run model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
      (prepare m k).H (prepare m k).Qg (grid_positive m k) (GeneralPaperScoreScaleParameters.labels_positive m k)
      classified classified.choice.proxy.value values columns).2≤
        profile model W m k Qv classified.choice.proxy.num classified.choice.proxy.den := by
  dsimp only
  have hMetadata := metadata_work model W m k b hb
  cases hc : (GeneralPaperProxyClassifier.classify m k b).choice.modify with
  | none =>
    simp only [GeneralPaperRetainedCompilerPairBits.run,hc]
    unfold profile
    omega
  | some side =>
    have hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none := by rw [hc]; simp
    cases side with
    | rich =>
      have hSide := GeneralPaperSourceModifiedCompilerBitPrice.column_work model W k Qv hm hQv weights hp hs b hb false
        hModify columns.rich values hRich hValues hW hDim hK hM hIndex hBatch hFinal hColumnsIndex
      simp only [GeneralPaperInitializerPreparedPoint.ownBudget,GeneralPaperInitializerPreparedPoint.opposingBudget,Bool.false_eq_true,ite_false] at hSide
      simp only [GeneralPaperRetainedCompilerPairBits.run,hc]
      unfold profile
      omega
    | poor =>
      have hSide := GeneralPaperSourceModifiedCompilerBitPrice.column_work model W k Qv hm hQv weights hp hs b hb true
        hModify columns.poor values hPoor hValues hW hDim hK hM hIndex hBatch hFinal hColumnsIndex
      simp only [GeneralPaperInitializerPreparedPoint.ownBudget,GeneralPaperInitializerPreparedPoint.opposingBudget,ite_true] at hSide
      simp only [GeneralPaperRetainedCompilerPairBits.run,hc]
      unfold profile
      omega

end Blotto.GeneralPaperSourceCompilerPairBitPrice
