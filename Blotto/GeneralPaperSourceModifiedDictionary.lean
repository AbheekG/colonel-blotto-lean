import Blotto.GeneralPaperDecodedPreparedSecurity

/-! The executed modified-defender branch returns the literal dictionary
with every unit/budget and continuous-security precondition discharged by
the actual full source. No dictionary or security oracle is supplied.
-/
namespace Blotto.GeneralPaperSourceModifiedDictionary
open GeneralPaperProxyParameters GeneralPaperSourceInitializer GeneralPaperInitializerPreparedPoint
open GeneralPaperDictionary GeneralPaperStrictScore GeneralPaperTransferPreparation
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

noncomputable def run {m : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (reciprocal : Bool) :=
  (GeneralPaperSourceEndpointBranch.run k Qv hQv weights hp hs b reciprocal).map GeneralPaperEndpointDictionary.dictionary

theorem opposing_positive (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    0<opposingBudget m k b reciprocal := by
  cases reciprocal
  · exact (GeneralPaperProxyClassifier.proxy_unit m k b hb).1
  · exact zero_lt_one

theorem scale_positive (m k : ℕ) (hm : 0<m) : 0<(GeneralPaperProxyParameters.prepare m k).S :=
  (Nat.mul_pos hm (GeneralPaperScoreScaleParameters.labels_positive m k)).trans_le
    (GeneralPaperScoreScaleParameters.scale_lower m k)

theorem of_contract {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (budget : ℝ) (hBudget : 0≤budget)
    (result : GeneralPaperSourceEndpointBranch.Result (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K)
    (hc : GeneralPaperSourceEndpointBranch.Contract (prepared k Qv hQv weights hp hs b reciprocal).dictionary
      (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S
      (prepared k Qv hQv weights hp hs b reciprocal).threshold budget result) :
    UnitDictionary (GeneralPaperEndpointDictionary.dictionary result)
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k) ∧
      security (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values budget
        (law (GeneralPaperEndpointDictionary.dictionary result) (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)).law≤
      security (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values (opposingBudget m k b reciprocal:ℝ)
        (law (GeneralPaperRowQuantizer.original (sourceRows k Qv weights b reciprocal))
          (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)).law+1/((prepare m k).K:ℝ)+(m:ℝ)/(prepare m k).S :=
  GeneralPaperDecodedPreparedSecurity.bound (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
    (sourceRows k Qv weights b reciprocal) (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
    (own_positive m k b hb reciprocal) (opposing_positive m k b hb reciprocal)
    (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S (scale_positive m k hm)
    (source_rows_feasible k Qv hm hQv weights hs b hb reciprocal) budget hBudget result hc

theorem rich {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .rich) :
    ∃ d,run k Qv hQv weights hp hs b false=some d ∧
      UnitDictionary d (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k) ∧
        d.label=(prepared k Qv hQv weights hp hs b false).dictionary.label ∧
          security (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values b
            (law d (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)).law≤
          security (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values (opposingBudget m k b false:ℝ)
            (law (GeneralPaperRowQuantizer.original (sourceRows k Qv weights b false))
              (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)).law+1/((prepare m k).K:ℝ)+(m:ℝ)/(prepare m k).S := by
  obtain ⟨result,hRun,hc⟩ := GeneralPaperSourceEndpointBranch.rich k Qv hm hQv weights hp hs b hb hModify
  have hd := of_contract k Qv hm hQv weights hp hs b hb false b hb.1.le result hc
  refine ⟨GeneralPaperEndpointDictionary.dictionary result,?_,hd.1,hc.1,hd.2⟩
  simp only [run,hRun,Option.map_some]

theorem poor {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor) :
    ∃ d,run k Qv hQv weights hp hs b true=some d ∧
      UnitDictionary d (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k) ∧
        d.label=(prepared k Qv hQv weights hp hs b true).dictionary.label ∧
          security (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values (1/b)
            (law d (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)).law≤
          security (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values (opposingBudget m k b true:ℝ)
            (law (GeneralPaperRowQuantizer.original (sourceRows k Qv weights b true))
              (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)).law+1/((prepare m k).K:ℝ)+(m:ℝ)/(prepare m k).S := by
  obtain ⟨result,hRun,hc⟩ := GeneralPaperSourceEndpointBranch.poor k Qv hm hQv weights hp hs b hb hModify
  have hd := of_contract k Qv hm hQv weights hp hs b hb true (1/b) (one_div_pos.mpr hb.1).le result hc
  refine ⟨GeneralPaperEndpointDictionary.dictionary result,?_,hd.1,hc.1,hd.2⟩
  simp only [run,hRun,Option.map_some]

end Blotto.GeneralPaperSourceModifiedDictionary
