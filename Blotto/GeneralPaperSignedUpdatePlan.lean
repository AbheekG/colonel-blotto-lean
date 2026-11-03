import Blotto.GeneralPaperNativeLossReference

/-! Actual signed-family updates: project a signed code to its unsigned
position, query the weak CDF, compare the returned row bid and compute the
integer increment. The sign marker and all query ranks are prepared/cached.
-/
namespace Blotto.GeneralPaperSignedUpdatePlan
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

def project (U code : ℕ) : ℕ := if code<U then code else code-U

def projected {m : ℕ} (U : ℕ) (codes : FixedArrayTable m ℕ) : FixedArrayTable m ℕ × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun q => (project U (codes.read q),16))

theorem projected_read {m : ℕ} (U : ℕ) (codes : FixedArrayTable m ℕ) (q : Fin m) :
    (projected U codes).1.read q=project U (codes.read q) := by
  rw [projected,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]

theorem projected_work {m : ℕ} (U : ℕ) (codes : FixedArrayTable m ℕ) : (projected U codes).2=58*m+18 := by
  rw [projected,PaperIndexedArrayConstruction.run_work,GeneralPaperEpochLevelArray.overhead]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  omega

structure Plan (k m : ℕ) where
  codes : FixedArrayTable m ℕ
  positions : FixedArrayTable m ℕ
  ranks : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))
  work : ℕ

def prepare {m : ℕ} (k U : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (codes : FixedArrayTable m ℕ) : Plan k m :=
  let positions := projected U codes
  let cuts := GeneralPaperCDFPairPlan.shiftCuts 1 positions.1
  let ranks := GeneralPaperRankCache.build k summary cuts.1
  ⟨codes,positions.1,ranks.1,positions.2+cuts.2+ranks.2+16⟩

structure Result where
  increment : ℕ
  count : ℕ
  positive : Bool
  hit : Bool
  work : ℕ

def evaluate {m : ℕ} (k U bid : ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (plan : Plan k m) (q : Fin m) : Result :=
  let queried := GeneralPaperRankedCDFQuery.cached k preparedPrefix plan.ranks q
  let positive := decide (plan.codes.read q<U)
  let hit := decide (bid≤plan.positions.read q)
  let increment := GeneralPaperRoundedLosses.signedIncrement (GeneralPaperSourceParameters.prepare k).meshDenominator queried.quotient positive hit
  ⟨increment,queried.quotient,positive,hit,queried.work+24⟩

theorem evaluate_count {m : ℕ} (k U bid : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (codes : FixedArrayTable m ℕ) (q : Fin m) :
    (evaluate k U bid preparedPrefix (prepare k U summary codes) q).count=
      GeneralPaperRankedCDFQuery.referenceCount k summary preparedPrefix (project U (codes.read q)+1) := by
  dsimp only [evaluate,prepare]
  rw [GeneralPaperRankedCDFQuery.cached_count,GeneralPaperCDFPairPlan.shift_read,projected_read]

theorem evaluate_increment {m : ℕ} (k U bid : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (codes : FixedArrayTable m ℕ) (q : Fin m) :
    (evaluate k U bid preparedPrefix (prepare k U summary codes) q).increment=
      GeneralPaperRoundedLosses.signedIncrement (GeneralPaperSourceParameters.prepare k).meshDenominator
        (GeneralPaperRankedCDFQuery.referenceCount k summary preparedPrefix (project U (codes.read q)+1))
        (decide (codes.read q<U)) (decide (bid≤project U (codes.read q))) := by
  dsimp only [evaluate,prepare]
  rw [GeneralPaperRankedCDFQuery.cached_count,GeneralPaperCDFPairPlan.shift_read,projected_read]

theorem evaluate_bounds {m : ℕ} (k U bid : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hTotal : 0<∑ r, values.read r) (codes : FixedArrayTable m ℕ) (q : Fin m) :
    (evaluate k U bid (GeneralPaperEpochPrefixArray.build values) (prepare k U summary codes) q).increment≤
      8*(GeneralPaperSourceParameters.prepare k).meshDenominator := by
  rw [evaluate_increment]
  exact GeneralPaperRoundedLosses.signed_increment_bound _ _
    (GeneralPaperRankedCDFQuery.reference_count_bound k summary values hTotal _) _ _

theorem evaluate_loss {m : ℕ} (k U bid : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hTotal : 0<∑ r, values.read r) (codes : FixedArrayTable m ℕ) (q : Fin m) :
    GeneralPaperGeometricLevels.executedLoss (GeneralPaperSourceParameters.prepare k).theta
      (evaluate k U bid (GeneralPaperEpochPrefixArray.build values) (prepare k U summary codes) q).increment=
    GeneralPaperRoundedLosses.signedLoss (GeneralPaperSourceParameters.prepare k).meshDenominator
      (GeneralPaperRankedCDFQuery.referenceCount k summary (GeneralPaperEpochPrefixArray.build values) (project U (codes.read q)+1))
      (decide (codes.read q<U)) (decide (bid≤project U (codes.read q))) := by
  rw [evaluate_increment,GeneralPaperSourceParameters.theta_mesh]
  exact GeneralPaperRoundedLosses.signed_increment_loss _ _ (GeneralPaperSourceParameters.mesh_positive k)
    (GeneralPaperRankedCDFQuery.reference_count_bound k summary values hTotal _) _ _

theorem evaluate_magnitude {m : ℕ} (k U bid : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hTotal : 0<∑ r, values.read r) (codes : FixedArrayTable m ℕ) (q : Fin m) :
    |(GeneralPaperGeometricLevels.executedLoss (GeneralPaperSourceParameters.prepare k).theta
      (evaluate k U bid (GeneralPaperEpochPrefixArray.build values) (prepare k U summary codes) q).increment:ℝ)|≤1 := by
  rw [evaluate_loss k U bid summary values hTotal codes q]
  have he := GeneralPaperRoundedLosses.signed_magnitude _ _ (GeneralPaperSourceParameters.mesh_positive k)
    (GeneralPaperRankedCDFQuery.reference_count_bound k summary values hTotal (project U (codes.read q)+1))
    (decide (codes.read q<U)) (decide (bid≤project U (codes.read q)))
  exact_mod_cast he

theorem prepare_work {m : ℕ} (k U : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (codes : FixedArrayTable m ℕ) : (prepare k U summary codes).work≤m*((35+k)*(12*(35+k)+34)+178)+70 := by
  have hr := GeneralPaperRankCache.build_work k summary (GeneralPaperCDFPairPlan.shiftCuts 1 (projected U codes).1).1
  change (projected U codes).2+(GeneralPaperCDFPairPlan.shiftCuts 1 (projected U codes).1).2+_+16≤_
  rw [projected_work,GeneralPaperCDFPairPlan.shift_work]
  nlinarith

theorem evaluate_work {m : ℕ} (k U bid : ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (plan : Plan k m) (q : Fin m) : (evaluate k U bid preparedPrefix plan q).work=12*(30+k)+66 := by
  unfold evaluate
  dsimp only
  rw [GeneralPaperRankedCDFQuery.cached_work]

end Blotto.GeneralPaperSignedUpdatePlan
