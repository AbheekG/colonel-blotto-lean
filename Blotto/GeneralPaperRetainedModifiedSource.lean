import Blotto.GeneralPaperRetainedCompilerPair

/-! Actual source data for the physical modified columns. Decoding is an
erased observer; no canonical compiler is executed by the native routine. -/
namespace Blotto.GeneralPaperRetainedModifiedSource
open GeneralPaperProxyParameters GeneralPaperInitializerPreparedPoint
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem data {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hColumns : GeneralPaperRowQuantizer.dictionary columns=GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal)
    (hValues : GeneralPaperRetainedFieldValues.selector values=GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
    (endpoint : Farey.Fraction) (hEndpoint : endpoint.value=(GeneralPaperProxyClassifier.classify m k b).choice.endpoint) :
    (GeneralPaperRetainedModifiedColumns.run model (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
      (prepare m k).H (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den
      (GeneralPaperScoreScaleParameters.labels_positive m k) columns values
      (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) reciprocal endpoint
      (GeneralPaperProxyClassifier.classify m k b).choice.endpoint).1.map GeneralPaperRowQuantizer.dictionary=
        GeneralPaperCheckedSourcePair.modified k Qv hQv weights hp hs b reciprocal := by
  have he := GeneralPaperRetainedCompilerSource.data model k Qv hm hQv weights hp hs b hb reciprocal
    columns values hColumns hValues endpoint hEndpoint
  exact (GeneralPaperRetainedModifiedColumns.data model _ _ _ _ _ _ columns values _ _ reciprocal endpoint _).trans
    (congrArg (Option.map GeneralPaperEndpointDictionary.dictionary) he)

end Blotto.GeneralPaperRetainedModifiedSource
