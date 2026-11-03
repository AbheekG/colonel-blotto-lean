import Blotto.GeneralPaperAdaptivePrefixJoin

/-! The actual adaptive snapshots and choices derive the four full-code
loss magnitudes and ordered variations. These bounds hold for each executed
round; extending finite histories and joining initial tree summaries to the
global regret/security proof remain separate dependencies.
-/
namespace Blotto.GeneralPaperAdaptiveLossBounds
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperEpochFieldPlan GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperEpochDeltas
open GeneralPaperEpochDeltaSemantics GeneralPaperAdaptiveEpoch GeneralPaperAdaptiveEpochHistory
open GeneralPaperGeometricLevels GeneralPaperOrderedVariation
set_option autoImplicit false
set_option maxHeartbeats 3500000

def IncrementBounds {k : ℕ} (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan) : Prop :=
  (∀ a, pIncrement state snapshot a≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator) ∧
  (∀ a, qIncrement state snapshot a≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator) ∧
  (∀ a, lambdaIncrement state snapshot choice a≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator) ∧
  (∀ a, muIncrement state snapshot choice a≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)

def Magnitudes {k : ℕ} (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan) : Prop :=
  (∀ a, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (pIncrement state snapshot a):ℝ)|≤2) ∧
  (∀ a, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (qIncrement state snapshot a):ℝ)|≤2) ∧
  (∀ a, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (lambdaIncrement state snapshot choice a):ℝ)|≤1) ∧
  (∀ a, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (muIncrement state snapshot choice a):ℝ)|≤1)

def Variations {k : ℕ} (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan) : Prop :=
  variation (fun a => (executedLoss (GeneralPaperSourceParameters.prepare k).theta (pIncrement state snapshot a):ℝ)) (state.plan.alphabet-1)≤4 ∧
  variation (fun a => (executedLoss (GeneralPaperSourceParameters.prepare k).theta (qIncrement state snapshot a):ℝ)) (state.plan.alphabet-1)≤4 ∧
  variation (fun a => (executedLoss (GeneralPaperSourceParameters.prepare k).theta (lambdaIncrement state snapshot choice a):ℝ)) (2*state.plan.alphabet-1)≤4 ∧
  variation (fun a => (executedLoss (GeneralPaperSourceParameters.prepare k).theta (muIncrement state snapshot choice a):ℝ)) (2*state.plan.alphabet-1)≤4

theorem increment_bounds {k : ℕ} (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan)
    (hPositive : Positive snapshot) (hCoherent : Coherent snapshot) : IncrementBounds state snapshot choice := by
  rcases hPositive with ⟨hp,hq,hl,hm⟩
  rcases hCoherent with ⟨cp,cq,cl,cm⟩
  unfold IncrementBounds pIncrement qIncrement lambdaIncrement muIncrement
  rw [cp,cq,cl,cm]
  refine ⟨?_,?_,?_,?_⟩
  · exact fun a => GeneralPaperQueryLossCounts.increment_bound k false _
      (GeneralPaperNativeLossReference.reference_bounds k state.plan.alphabet _ _ _ _ hq hl a)
  · exact fun a => GeneralPaperQueryLossCounts.increment_bound k true _
      (GeneralPaperNativeLossReference.reference_bounds k state.plan.alphabet _ _ _ _ hp hm a)
  · intro a
    exact GeneralPaperRoundedLosses.signed_increment_bound _ _
      (GeneralPaperRankedCDFQuery.reference_count_bound k _ _ hp _) _ _
  · intro a
    exact GeneralPaperRoundedLosses.signed_increment_bound _ _
      (GeneralPaperRankedCDFQuery.reference_count_bound k _ _ hq _) _ _

theorem signed_magnitude (k U bid : ℕ) (summary values : Summary k) (hTotal : 0<∑ r, values.read r) (code : ℕ) :
    |(executedLoss (GeneralPaperSourceParameters.prepare k).theta
      (GeneralPaperSignedUpdateReference.increment k U bid summary (GeneralPaperEpochPrefixArray.build values) code):ℝ)|≤1 := by
  rw [GeneralPaperSignedUpdateReference.increment_loss k U bid summary values hTotal code]
  unfold GeneralPaperSignedUpdateReference.loss
  exact_mod_cast GeneralPaperRoundedLosses.signed_magnitude _ _ (GeneralPaperSourceParameters.mesh_positive k)
    (GeneralPaperRankedCDFQuery.reference_count_bound k summary values hTotal _) _ _

theorem magnitudes {k : ℕ} (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan)
    (hPositive : Positive snapshot) (hCoherent : Coherent snapshot) : Magnitudes state snapshot choice := by
  rcases hPositive with ⟨hp,hq,hl,hm⟩
  rcases hCoherent with ⟨cp,cq,cl,cm⟩
  unfold Magnitudes pIncrement qIncrement lambdaIncrement muIncrement
  rw [cp,cq,cl,cm]
  exact ⟨fun a => GeneralPaperQueryLossCounts.executed_magnitude k false _
      (GeneralPaperNativeLossReference.reference_bounds k state.plan.alphabet _ _ _ _ hq hl a),
    fun a => GeneralPaperQueryLossCounts.executed_magnitude k true _
      (GeneralPaperNativeLossReference.reference_bounds k state.plan.alphabet _ _ _ _ hp hm a),
    signed_magnitude k state.plan.alphabet choice.candidateBid _ _ hp,
    signed_magnitude k state.plan.alphabet choice.responseBid _ _ hq⟩

theorem variations {k : ℕ} (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan)
    (hPositive : Positive snapshot) (hCoherent : Coherent snapshot) (hOrdered : Ordered state.plan) (hCodes : CodesValid state.plan) :
    Variations state snapshot choice := by
  rcases hPositive with ⟨hp,hq,hl,hm⟩
  rcases hCoherent with ⟨cp,cq,cl,cm⟩
  have hx : choice.candidateBid<state.plan.alphabet := hCodes.2.2.2.2.1 choice.candidate
  have hy : choice.responseBid<state.plan.alphabet := hCodes.2.2.2.2.2 choice.response
  have hU : 0<state.plan.alphabet := (Nat.zero_le choice.candidateBid).trans_lt hx
  unfold Variations pIncrement qIncrement lambdaIncrement muIncrement
  rw [cp,cq,cl,cm]
  exact ⟨GeneralPaperNativeLossReference.executed_variation k state.plan.alphabet _ false _ _ _ _ hOrdered.2.1 hOrdered.2.2.1 hq hl,
    GeneralPaperNativeLossReference.executed_variation k state.plan.alphabet _ true _ _ _ _ hOrdered.1 hOrdered.2.2.2 hp hm,
    GeneralPaperSignedUpdateReference.executed_variation k state.plan.alphabet choice.candidateBid hU hx _ _ hOrdered.1 hp hCodes.1,
    GeneralPaperSignedUpdateReference.executed_variation k state.plan.alphabet choice.responseBid hU hy _ _ hOrdered.2.1 hq hCodes.2.1⟩

theorem executed_magnitudes {n : ℕ} (lambda k : ℕ) (select : Selector n k)
    (plans : FixedArrayTable n (Plan k)) (time : ℕ) (hTime : time≤(GeneralPaperTrajectoryParameters.prepare lambda k).period) (j : Fin n) :
    Magnitudes (fieldAt (GeneralPaperPreparedPowers.prepare lambda k) select (initial plans) time j)
      (snapshotAt (GeneralPaperPreparedPowers.prepare lambda k) select (initial plans) time j)
      (choiceAt (GeneralPaperPreparedPowers.prepare lambda k) select (initial plans) time j) :=
  magnitudes _ _ _
    (GeneralPaperEpochSnapshot.take_positive lambda k _ (GeneralPaperAdaptiveEpochBounds.execute_cap lambda k select plans time hTime j))
    (GeneralPaperEpochSnapshot.take_coherent _ _)

theorem executed_variations {n : ℕ} (lambda k : ℕ) (select : Selector n k)
    (plans : FixedArrayTable n (Plan k)) (time : ℕ) (hTime : time≤(GeneralPaperTrajectoryParameters.prepare lambda k).period) (j : Fin n)
    (hOrdered : Ordered (plans.read j)) (hCodes : CodesValid (plans.read j)) :
    Variations (fieldAt (GeneralPaperPreparedPowers.prepare lambda k) select (initial plans) time j)
      (snapshotAt (GeneralPaperPreparedPowers.prepare lambda k) select (initial plans) time j)
      (choiceAt (GeneralPaperPreparedPowers.prepare lambda k) select (initial plans) time j) := by
  have he : (fieldAt (GeneralPaperPreparedPowers.prepare lambda k) select (initial plans) time j).plan=plans.read j :=
    GeneralPaperAdaptiveEpochBounds.initial_plan _ select plans time j
  exact variations _ _ _
    (GeneralPaperEpochSnapshot.take_positive lambda k _ (GeneralPaperAdaptiveEpochBounds.execute_cap lambda k select plans time hTime j))
    (GeneralPaperEpochSnapshot.take_coherent _ _)
    (by rw [he]; exact hOrdered) (by rw [he]; exact hCodes)

end Blotto.GeneralPaperAdaptiveLossBounds
