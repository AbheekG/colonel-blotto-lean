import Blotto.GeneralPaperEncodedNatArray

/-! All eight stored level arrays and all eight generated delta arrays.
Plans are retained shared references and counted in the cache workspace.
Actual reached states supply level and partition-count premises. -/
namespace Blotto.GeneralPaperEncodedEpochLevels
open GeneralPaperEpochFieldState
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def Counts {k : ℕ} (state : GeneralPaperEpochFieldState.State k) : Prop :=
  state.plan.pCells.partition.count≤GeneralPaperBatchCounterPrice.limit k ∧
  state.plan.qCells.partition.count≤GeneralPaperBatchCounterPrice.limit k ∧
  state.plan.lambdaCells.partition.count≤GeneralPaperBatchCounterPrice.limit k ∧
  state.plan.muCells.partition.count≤GeneralPaperBatchCounterPrice.limit k

theorem actual_counts {m k : ℕ} (cache : Cache m k) (state : GeneralPaperEpochFieldState.State k) (j : Fin m)
    (hp : state.plan=cache.plans.read j) : Counts state := by
  unfold Counts
  rw [hp]
  exact ⟨GeneralPaperActualEpochInstructions.cell_count .p cache j,GeneralPaperActualEpochInstructions.cell_count .q cache j,
    GeneralPaperActualEpochInstructions.cell_count .lambda cache j,GeneralPaperActualEpochInstructions.cell_count .mu cache j⟩

def fieldFootprint {k : ℕ} (W : ℕ) (state : GeneralPaperEpochFieldState.State k) : ℕ :=
  GeneralPaperEncodedNatArray.footprint W state.pOccurrences+GeneralPaperEncodedNatArray.footprint W state.qOccurrences+
  GeneralPaperEncodedNatArray.footprint W state.lambdaOccurrences+GeneralPaperEncodedNatArray.footprint W state.muOccurrences+
  GeneralPaperEncodedNatArray.footprint W state.pCells+GeneralPaperEncodedNatArray.footprint W state.qCells+
  GeneralPaperEncodedNatArray.footprint W state.lambdaCells+GeneralPaperEncodedNatArray.footprint W state.muCells+64*W

def fieldProfile (W m lambda k Qv : ℕ) : ℕ :=
  (4*(GeneralPaperSourceParameters.prepare k).summarySize+4*GeneralPaperBatchCounterPrice.limit k)*
    (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+320*W

theorem field_bound {k : ℕ} (W m lambda Qv : ℕ) (state : GeneralPaperEpochFieldState.State k)
    (hc : Counts state) (hb : Bounded state (GeneralPaperPowerPrecision.levelBound lambda k)) :
    fieldFootprint W state≤fieldProfile W m lambda k Qv := by
  have hp := GeneralPaperEncodedNatArray.level W m lambda k Qv state.pOccurrences hb.1
  have hq := GeneralPaperEncodedNatArray.level W m lambda k Qv state.qOccurrences hb.2.1
  have hl := GeneralPaperEncodedNatArray.level W m lambda k Qv state.lambdaOccurrences hb.2.2.1
  have hu := GeneralPaperEncodedNatArray.level W m lambda k Qv state.muOccurrences hb.2.2.2.1
  have pc := (GeneralPaperEncodedNatArray.level W m lambda k Qv state.pCells hb.2.2.2.2.1).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc.1) _)
  have qc := (GeneralPaperEncodedNatArray.level W m lambda k Qv state.qCells hb.2.2.2.2.2.1).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc.2.1) _)
  have lc := (GeneralPaperEncodedNatArray.level W m lambda k Qv state.lambdaCells hb.2.2.2.2.2.2.1).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc.2.2.1) _)
  have mc := (GeneralPaperEncodedNatArray.level W m lambda k Qv state.muCells hb.2.2.2.2.2.2.2).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc.2.2.2) _)
  unfold fieldFootprint fieldProfile
  nlinarith only [hp,hq,hl,hu,pc,qc,lc,mc]

def familyFootprint {m k : ℕ} (W : ℕ) (fields : GeneralPaperAdaptiveEpoch.Fields m k) : ℕ :=
  (∑ j, fieldFootprint W (fields.read j))+m*W+64*W

def profile (W m lambda k Qv : ℕ) : ℕ := m*fieldProfile W m lambda k Qv+m*W+64*W

theorem family_bound {m k : ℕ} (W lambda Qv : ℕ) (fields : GeneralPaperAdaptiveEpoch.Fields m k)
    (hc : ∀ j,Counts (fields.read j)) (hb : ∀ j,Bounded (fields.read j) (GeneralPaperPowerPrecision.levelBound lambda k)) :
    familyFootprint W fields≤profile W m lambda k Qv := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => field_bound W m lambda Qv (fields.read j) (hc j) (hb j))
  have h := Nat.add_le_add_right (Nat.add_le_add_right hs (m*W)) (64*W)
  simpa only [familyFootprint,profile,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using h

theorem selected {m k : ℕ} (W Qv : ℕ) (cache : Cache m k) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    familyFootprint W (stateAt (GeneralPaperCatalogueEpochRun.selected cache Qv weights Bc Br) time).fields≤
      profile W m cache.alphabet.lambda k Qv :=
  family_bound W cache.alphabet.lambda Qv _ (fun j => actual_counts cache _ j ((stateAt _ time).plan_spec j))
    (fun j => selected_cap cache Qv weights Bc Br time ht j)

def deltaView {k : ℕ} {state : GeneralPaperEpochFieldState.State k} (delta : Deltas state) : GeneralPaperEpochFieldState.State k :=
  ⟨state.plan,delta.pOccurrences,delta.qOccurrences,delta.lambdaOccurrences,delta.muOccurrences,
    delta.pCells,delta.qCells,delta.lambdaCells,delta.muCells⟩

theorem delta_bound {k : ℕ} (W m lambda Qv B : ℕ) (state : GeneralPaperEpochFieldState.State k) (delta : Deltas state)
    (hc : Counts state) (hb : delta.Bounded B) (hB : B≤GeneralPaperPowerPrecision.levelBound lambda k) :
    fieldFootprint W (deltaView delta)≤fieldProfile W m lambda k Qv := by
  apply field_bound W m lambda Qv (deltaView delta) hc
  rcases hb with ⟨hp,hq,hl,hu,pc,qc,lc,mc⟩
  exact ⟨fun i => (hp i).trans hB,fun i => (hq i).trans hB,fun i => (hl i).trans hB,fun i => (hu i).trans hB,
    fun i => (pc i).trans hB,fun i => (qc i).trans hB,fun i => (lc i).trans hB,fun i => (mc i).trans hB⟩

theorem generated {m k : ℕ} (W Qv : ℕ) (cache : Cache m k) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    let current := GeneralPaperCatalogueEpochRun.selected cache Qv weights Bc Br
    fieldFootprint W (deltaView (deltaAt current time j))≤fieldProfile W m cache.alphabet.lambda k Qv := by
  let current := GeneralPaperCatalogueEpochRun.selected cache Qv weights Bc Br
  have hg := GeneralPaperEpochDeltas.generated_bound (fieldAt current time j) (snapshotAt current time j) (choiceAt current time j)
    (selected_positive cache Qv weights Bc Br time ht j) (snapshot_coherent current time j)
  have hr := GeneralPaperTrajectoryParameters.rows_positive cache.alphabet.lambda k
  have hB : 8*(GeneralPaperSourceParameters.prepare k).meshDenominator≤GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k := by
    unfold GeneralPaperPowerPrecision.levelBound
    nlinarith only [hr]
  exact delta_bound W m cache.alphabet.lambda Qv _ _ _
    (actual_counts cache _ j (field_plan current time j)) hg hB

end Blotto.GeneralPaperEncodedEpochLevels
