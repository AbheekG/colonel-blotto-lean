import Blotto.GeneralPaperStoredMaximumStorage
import Blotto.GeneralPaperScoreResidencyRates

/-! Terminal strict-preparation/maximum-guard storage. The actual matrix,
DP table, normalized values and three short budget scalars remain resident.
The maximum pass, budget-division scratch, return-work metadata and actual
guard comparison are joined. Physical-column payloads are borrowed from
the outer source/compiler scope; endpoint continuation is separate. -/
namespace Blotto.GeneralPaperSourceGuardStorage
open GeneralPaperProxyParameters GeneralPaperInitializerPreparedPoint GeneralPaperExactScoreDP
open GeneralPaperEncodedScalarStorage GeneralPaperScoreTableStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def price (model : RationalCostModel) (W depth m K S C D V A : ℕ) : ℕ :=
  GeneralPaperRetainedTransferPrice.bitProfile model W depth S C D V A m K

def metadataCap (model : RationalCostModel) (W depth m K S C D V A : ℕ) : ℕ :=
  S+1+price model W depth m K S C D V A+model.rat (1+binaryWordWidth S)+32*W

def parentMetadata {T m K : ℕ} (model : RationalCostModel) (W depth S : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) : List ℕ :=
  let matrix := GeneralPaperPhysicalScoreMatrix.run true model W depth columns (GeneralPaperRetainedFieldValues.selector values) S
  let table := GeneralPaperRetainedTransferPreparation.dp true model W S matrix.1.data.toList
  let selected := GeneralPaperRetainedTransferPreparation.threshold true model W table.1 (opposing/own)
  let maximum := GeneralPaperStoredScoreMaximum.run true model W hK matrix.1
  let retained := GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing
  [retained.1.prepared.threshold,retained.1.maximum,retained.2,matrix.2,table.2,selected.2,maximum.2,
    matrix.2+table.2,matrix.2+table.2+selected.2,matrix.2+table.2+selected.2+maximum.2,
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) opposing own,
    GeneralPaperRetainedCompilerBranchBits.thresholdPrice model W retained.1.prepared.threshold retained.1.maximum]

def window {T m K : ℕ} (model : RationalCostModel) (W depth S : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (loadCount : ℕ) (hl : loadCount≤m) (sumCount : ℕ) (hc : sumCount≤m) : ℕ :=
  let retained := GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing
  GeneralPaperScoreResidentPhases.resident model W depth S columns values+
    tableFootprint W retained.1.prepared.table+GeneralPaperEncodedRationalRows.rowFootprint W values.values+
    rationalWordWidth own+rationalWordWidth opposing+rationalWordWidth retained.1.budget+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) opposing own+
    GeneralPaperStoredMaximumStorage.window model W hK retained.1.matrix loadCount hl sumCount hc+
    fields W (parentMetadata model W depth S hK columns values own opposing)+
    GeneralPaperRetainedCompilerBranchBits.thresholdPrice model W retained.1.prepared.threshold retained.1.maximum+256*W

def profile (model : RationalCostModel) (W depth m K S C D V A : ℕ) : ℕ :=
  GeneralPaperScoreResidentPhases.residentProfile W m K S A+tableProfile W K S m (GeneralPaperScoreBitPrimitive.resourceWidth A m)+
    GeneralPaperEncodedRationalRows.rowProfile W m V+3*(1+2*(C+D))+2*model.rat (1+2*(C+D))+
    GeneralPaperStoredMaximumStorage.profile model W m K S+
    12*(natBits (metadataCap model W depth m K S C D V A)+W)+32*W+
    (model.rat (1+binaryWordWidth S)+32*W)+256*W

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W depth S C D V A : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (hOwn : RationalHeight own C) (hOpposing : RationalHeight opposing D)
    (hv : ∀ j,RationalHeight (values.values.read j) V) (ha : ∀ j l,RationalHeight ((columns.read j).anchors.read l) A)
    (hCap : S<2^depth) (hW : 1≤W) (hLabel : binaryWordWidth (K+1)≤W)
    (hField : binaryWordWidth (m+1)≤W) (hScore : binaryWordWidth (S+2)≤W)
    (loadCount : ℕ) (hl : loadCount≤m) (sumCount : ℕ) (hc : sumCount≤m) :
    window model W depth S hK columns values own opposing loadCount hl sumCount hc≤profile model W depth m K S C D V A := by
  let retained := GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing
  let matrix := GeneralPaperPhysicalScoreMatrix.run true model W depth columns (GeneralPaperRetainedFieldValues.selector values) S
  let table := GeneralPaperRetainedTransferPreparation.dp true model W S matrix.1.data.toList
  let selected := GeneralPaperRetainedTransferPreparation.threshold true model W table.1 (opposing/own)
  let maximum := GeneralPaperStoredScoreMaximum.run true model W hK matrix.1
  have hTimeShape : retained.2=matrix.2+table.2+selected.2+maximum.2+
      GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) opposing own+
        64*(m+1)*GeneralPaperSummaryArrayExecution.arrayWord W (m+K+S)+64*GeneralPaperSummaryArrayExecution.arrayWord W (m+K+S) := rfl
  have hResident := GeneralPaperScoreResidentPhases.resident_bound model W depth S A hK columns values hCap ha
  have hTable := GeneralPaperSourceScoreStorage.table_return model W depth S A hK columns values own opposing hCap ha
  have hValues := GeneralPaperEncodedRationalRows.row_bound W V values.values hv
  have hBudget : RationalHeight (opposing/own) (C+D) := (hOpposing.div hOwn).mono (by omega)
  have wOwn := rationalWordWidth_of_height (hOwn.mono (show C≤C+D by omega))
  have wOpp := rationalWordWidth_of_height (hOpposing.mono (show D≤C+D by omega))
  have wBudget := rationalWordWidth_of_height hBudget
  have hDivision := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b)
    opposing own (1+2*(C+D)) wOpp wOwn wBudget
  have hTop : (∑ j,((retained.1.matrix.read j).read (GeneralPaperScoreMaximum.topLabel K hK)).1)≤S := by
    change (∑ j,(((GeneralPaperPhysicalScoreMatrix.run true model W depth columns
      (GeneralPaperRetainedFieldValues.selector values) S).1.read j).read (GeneralPaperScoreMaximum.topLabel K hK)).1)≤S
    rw [GeneralPaperPhysicalScoreMatrix.data true model W depth columns _ S hK hCap]
    simpa only [FixedArrayTable.read_ofFn,GeneralPaperStrictScore.totalScore] using
      GeneralPaperComputedThreshold.totalScore_le (GeneralPaperRetainedFieldValues.selector values) S hK
        (fun _ => GeneralPaperScoreMaximum.topLabel K hK)
  have hMaximum := GeneralPaperStoredMaximumStorage.bounded model W S hK retained.1.matrix hTop loadCount hl sumCount hc
  have hThreshold := GeneralPaperSourceStrictPreparationBits.threshold_bound model W depth S hK columns values own opposing
  have hMaxValue := GeneralPaperSourceStrictPreparationBits.maximum_bound model W depth S hK columns values own opposing hCap
  have hTime := GeneralPaperRetainedTransferPrice.bit_work model W depth S C D V A hK columns values own opposing
    hOwn hOpposing hv ha hCap hW hLabel hField hScore
  change retained.2≤price model W depth m K S C D V A at hTime
  change retained.1.prepared.threshold≤S at hThreshold
  change retained.1.maximum≤S at hMaxValue
  have hGuard := GeneralPaperSourceStrictPreparationBits.threshold_price model W depth S hK columns values own opposing hCap
  change GeneralPaperRetainedCompilerBranchBits.thresholdPrice model W retained.1.prepared.threshold retained.1.maximum≤_ at hGuard
  have hf := fields_bound W (natBits (metadataCap model W depth m K S C D V A))
    (parentMetadata model W depth S hK columns values own opposing) (by
      intro n hn
      change n∈[retained.1.prepared.threshold,retained.1.maximum,retained.2,matrix.2,table.2,selected.2,maximum.2,
        matrix.2+table.2,matrix.2+table.2+selected.2,matrix.2+table.2+selected.2+maximum.2,
        GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) opposing own,
        GeneralPaperRetainedCompilerBranchBits.thresholdPrice model W retained.1.prepared.threshold retained.1.maximum] at hn
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤12*(natBits (metadataCap model W depth m K S C D V A)+W)+32*W at hf
  change rationalWordWidth retained.1.budget≤1+2*(C+D) at wBudget
  change tableFootprint W retained.1.prepared.table≤_ at hTable
  change GeneralPaperScoreResidentPhases.resident model W depth S columns values+tableFootprint W retained.1.prepared.table+
    GeneralPaperEncodedRationalRows.rowFootprint W values.values+rationalWordWidth own+rationalWordWidth opposing+rationalWordWidth retained.1.budget+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) opposing own+
    GeneralPaperStoredMaximumStorage.window model W hK retained.1.matrix loadCount hl sumCount hc+
    fields W (parentMetadata model W depth S hK columns values own opposing)+
    GeneralPaperRetainedCompilerBranchBits.thresholdPrice model W retained.1.prepared.threshold retained.1.maximum+256*W≤_
  unfold profile
  omega

def sourceProfile (model : RationalCostModel) (W m k Qv : ℕ) : ℕ :=
  profile model W (GeneralPaperScoreScaleParameters.prepare m k).depth m (prepare m k).K (prepare m k).S
    (binaryWordWidth (prepare m k).qbar) (binaryWordWidth (prepare m k).qbar) (binaryWordWidth Qv)
    (GeneralPaperSourceScoreHeights.anchorHeight m k)

theorem actual {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hColumns : GeneralPaperRowQuantizer.dictionary columns=GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal)
    (hValues : GeneralPaperRetainedFieldValues.selector values=GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
    (hW : 1≤W) (hLabel : binaryWordWidth ((prepare m k).K+1)≤W) (hField : binaryWordWidth (m+1)≤W)
    (hScore : binaryWordWidth ((prepare m k).S+2)≤W)
    (loadCount : ℕ) (hl : loadCount≤m) (sumCount : ℕ) (hc : sumCount≤m) :
    window model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
      (GeneralPaperScoreScaleParameters.labels_positive m k) columns values (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
      loadCount hl sumCount hc≤sourceProfile model W m k Qv := by
  apply bounded model W _ _ _ _ _ _ (GeneralPaperScoreScaleParameters.labels_positive m k) columns values _ _
    (GeneralPaperSourceScoreHeights.own_height m k b hb reciprocal)
    (GeneralPaperSourceStrictPreparationBits.opposing_height m k b hb reciprocal) _
    (GeneralPaperSourceScoreResidents.anchors k Qv hQv weights hp hs b hb reciprocal columns hColumns)
    (GeneralPaperScoreScaleParameters.score_cap m k) hW hLabel hField hScore loadCount hl sumCount hc
  intro j
  change RationalHeight ((GeneralPaperRetainedFieldValues.selector values).weight j) _
  rw [hValues]
  exact GeneralPaperSourceScoreHeights.value_height Qv hQv weights hp hs j

end Blotto.GeneralPaperSourceGuardStorage
