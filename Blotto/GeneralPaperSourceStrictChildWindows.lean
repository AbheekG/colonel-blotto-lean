import Blotto.GeneralPaperSourceStrictConstructorReachedRates
import Blotto.GeneralPaperGuardMinimumStorageRates

/-! Actual strict-preparation child windows: initial empty-DP-table
construction with retained matrix and recursive callers, the full strict
threshold scan and the stored-maximum/guard window. All original source
heights and native column/value identities derive their premises. -/
namespace Blotto.GeneralPaperSourceStrictChildWindows
open GeneralPaperProxyParameters GeneralPaperInitializerPreparedPoint
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384

noncomputable def initialWindow {T m : ℕ} (model : RationalCostModel) (W k : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (count : ℕ) (hc : count≤(prepare m k).S+1) : ℕ :=
  GeneralPaperScoreResidentPhases.resident model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S columns values+
    GeneralPaperScoreLifetimeStorage.callerFrames model W (prepare m k).S
      (GeneralPaperSourceScoreStorage.matrixFields model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S columns values)+
    GeneralPaperScoreInitialStorage.window model W (prepare m k).K (prepare m k).S count hc

def InitialBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) : Prop :=
  ∀ count (hc : count≤(prepare m k).S+1),initialWindow model W k columns values count hc≤limit

def ThresholdBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) : Prop :=
  GeneralPaperScoreResidentPhases.thresholdWindow model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) columns values own opposing≤limit

def MaximumBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) : Prop :=
  ∀ load (hl : load≤m) sum (hs : sum≤m),GeneralPaperSourceGuardStorage.window model W
    (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k)
    columns values own opposing load hl sum hs≤limit

theorem initial_mono {T m : ℕ} (model : RationalCostModel) (W k B C : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (hBC : B≤C) (h : InitialBound model W k B columns values) :
    InitialBound model W k C columns values := fun n hn => (h n hn).trans hBC

theorem threshold_mono {T m : ℕ} (model : RationalCostModel) (W k B C : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) (hBC : B≤C)
    (h : ThresholdBound model W k B columns values own opposing) : ThresholdBound model W k C columns values own opposing := h.trans hBC

theorem maximum_mono {T m : ℕ} (model : RationalCostModel) (W k B C : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) (hBC : B≤C)
    (h : MaximumBound model W k B columns values own opposing) : MaximumBound model W k C columns values own opposing :=
  fun load hl sum hs => (h load hl sum hs).trans hBC

theorem source_components {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) :
    let columns := GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal
    let values := (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
    let own := ownBudget m k b reciprocal
    let opposing := opposingBudget m k b reciprocal
    InitialBound model W k (GeneralPaperScoreResidencyRates.initialProfile model W m k) columns values ∧
      ThresholdBound model W k (GeneralPaperSourceScoreResidents.thresholdProfile model W m k) columns values own opposing ∧
      MaximumBound model W k (GeneralPaperSourceGuardStorage.sourceProfile model W m k Qv) columns values own opposing := by
  let columns := GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal
  let values := (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
  have hc := GeneralPaperSourceEnclosingOwners.column_data model W k Qv weights b reciprocal
  have hv := GeneralPaperRetainedFieldValues.selector_data true model W Qv hQv weights hp hs
  refine ⟨?_,?_,?_⟩
  · intro count hCount
    exact GeneralPaperScoreResidentPhases.initial_with_matrix model W (GeneralPaperScoreScaleParameters.prepare m k).depth
      (prepare m k).S (GeneralPaperSourceScoreHeights.anchorHeight m k) (GeneralPaperScoreScaleParameters.labels_positive m k)
      columns values (GeneralPaperScoreScaleParameters.score_cap m k)
      (GeneralPaperSourceScoreResidents.anchors k Qv hQv weights hp hs b hb reciprocal columns hc) hW hIndex count hCount
  · exact GeneralPaperSourceScoreResidents.threshold model W k Qv hQv weights hp hs b hb reciprocal columns values hc
  · intro load hl sum hSum
    exact GeneralPaperSourceGuardStorage.actual model W k Qv hQv weights hp hs b hb reciprocal columns values hc hv hW hK hM hIndex load hl sum hSum

end Blotto.GeneralPaperSourceStrictChildWindows
