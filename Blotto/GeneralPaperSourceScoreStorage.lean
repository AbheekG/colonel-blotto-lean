import Blotto.GeneralPaperScoreLifetimeStorage
import Blotto.GeneralPaperSourceStrictPreparationBits

/-! Apply the exact-score storage bounds to the actual retained physical
source matrix and table. Anchor heights are derived from the checked source
dictionary. Partial scans, table construction prefixes and actual recursive
DP layers are covered before any endpoint or acceptance assumption. Matrix
construction/residency and the surrounding compiler remain separate joins. -/
namespace Blotto.GeneralPaperSourceScoreStorage
open GeneralPaperProxyParameters GeneralPaperMinimum GeneralPaperExactScoreDP
open GeneralPaperScoreTableStorage GeneralPaperScoreLifetimeStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def matrixFields {T m K : ℕ} (model : RationalCostModel) (W depth S : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) : List (Field K) :=
  (GeneralPaperPhysicalScoreMatrix.run true model W depth columns (GeneralPaperRetainedFieldValues.selector values) S).1.data.toList

theorem fields_length {T m K : ℕ} (model : RationalCostModel) (W depth S : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) : (matrixFields model W depth S columns values).length=m := by
  unfold matrixFields
  rw [Array.length_toList,FixedArrayTable.size]

theorem fields_height {T m K : ℕ} (model : RationalCostModel) (W depth S A : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (hCap : S<2^depth)
    (ha : ∀ j l,RationalHeight ((columns.read j).anchors.read l) A) :
    CostHeight (matrixFields model W depth S columns values) A := by
  unfold matrixFields
  rw [GeneralPaperRetainedTransferPreparation.fields_data true model W depth S columns _ hK hCap]
  exact GeneralPaperQuantizedHeight.fields_cost_height (GeneralPaperRowQuantizer.dictionary columns)
    (GeneralPaperRetainedFieldValues.selector values) S A ha

theorem table_return {T m K : ℕ} (model : RationalCostModel) (W depth S A : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) (hCap : S<2^depth)
    (ha : ∀ j l,RationalHeight ((columns.read j).anchors.read l) A) :
    tableFootprint W (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1.prepared.table≤
      tableProfile W K S m (GeneralPaperScoreBitPrimitive.resourceWidth A m) := by
  change tableFootprint W (GeneralPaperRetainedTransferPreparation.dp true model W S
    (matrixFields model W depth S columns values)).1≤_
  rw [GeneralPaperRetainedTransferPreparation.dp_data]
  exact table_bound W m _ _ (GeneralPaperScoreSelectionStorage.run_bounded S A m _
    (fields_height model W depth S A hK columns values hCap ha) (fields_length model W depth S columns values).le)

theorem source_fields_height {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hColumns : GeneralPaperRowQuantizer.dictionary columns=GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal) :
    CostHeight (matrixFields model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S columns values)
      (GeneralPaperSourceScoreHeights.anchorHeight m k) := by
  apply fields_height model W _ _ _ (GeneralPaperScoreScaleParameters.labels_positive m k) columns values
    (GeneralPaperScoreScaleParameters.score_cap m k)
  intro j l
  change RationalHeight ((GeneralPaperRowQuantizer.dictionary columns).anchor j l) _
  rw [hColumns,GeneralPaperSourceUnchangedDictionary.eq_prepared k Qv hQv weights hp hs b reciprocal]
  exact GeneralPaperSourceScoreHeights.prepared_anchors k Qv hQv weights hp hs b hb reciprocal j l

def profile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  layerProfile model W (prepare m k).K (prepare m k).S (GeneralPaperSourceScoreHeights.anchorHeight m k) m

theorem actual_layer {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hColumns : GeneralPaperRowQuantizer.dictionary columns=GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal)
    (hW : 1≤W) (hIndex : binaryWordWidth ((prepare m k).S+2)≤W)
    (field : Field (prepare m k).K) (rest : List (Field (prepare m k).K))
    (hSub : (field::rest).Sublist (matrixFields model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S columns values))
    (count : ℕ) (hc : count≤(prepare m k).S+1) (s : Fin ((prepare m k).S+1))
    (xs : List (Fin (prepare m k).K)) (hXs : xs.length≤(prepare m k).K) :
    callerFrames model W (prepare m k).S
      (matrixFields model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S columns values)+
      GeneralPaperScoreConstructionStorage.stepWindow model W field rest count hc s xs≤profile model W m k :=
  GeneralPaperScoreLifetimeStorage.actual_layer model W _ m _
    (source_fields_height model W k Qv hQv weights hp hs b hb reciprocal columns values hColumns)
    (fields_length model W _ _ columns values).le hW hIndex field rest hSub count hc s xs hXs

end Blotto.GeneralPaperSourceScoreStorage
