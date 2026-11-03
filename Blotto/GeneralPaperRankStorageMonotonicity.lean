import Blotto.GeneralPaperActualRankPlanConstructionStorage

/-! Native query-count monotonicity lifts actual constructed cell counts
to their derived source limits. These inequalities are erased; no runtime
maximum, census, annotation or calibration traversal is introduced. -/
namespace Blotto.GeneralPaperRankStorageMonotonicity
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem nat_word (n N : ℕ) (h : n≤N) : natBits n≤natBits N := Nat.add_le_add_left (binaryWordWidth_mono h) 1

theorem native_array (W V n N : ℕ) (h : n≤N) :
    GeneralPaperNativeNatFillStorage.profile W n V≤GeneralPaperNativeNatFillStorage.profile W N V := by
  have hw := nat_word (n+1) (N+1) (Nat.add_le_add_right h 1)
  have hf := GeneralPaperBoundaryConstructionStorage.frames_mono W n N h
  unfold GeneralPaperNativeNatFillStorage.profile
  gcongr

theorem rank_frames (W d n N : ℕ) (h : n≤N) :
    GeneralPaperRankConstructionStorage.frames W n d≤GeneralPaperRankConstructionStorage.frames W N d := by
  have hw := nat_word (n+1) (N+1) (Nat.add_le_add_right h 1)
  unfold GeneralPaperRankConstructionStorage.frames
  gcongr

theorem rank_record (W k V n N : ℕ) (h : n≤N) :
    GeneralPaperRankRecordConstructionStorage.recordProfile W n k V≤GeneralPaperRankRecordConstructionStorage.recordProfile W N k V := by
  have hw := GeneralPaperPlanProfileMonotonicity.rank_width n N (35+k) V h
  unfold GeneralPaperRankRecordConstructionStorage.recordProfile
  gcongr

theorem rank_partial (model : RationalCostModel) (W k V n N : ℕ) (h : n≤N) :
    GeneralPaperRankConstructionStorage.profile model W n k V≤GeneralPaperRankConstructionStorage.profile model W N k V := by
  have hw := GeneralPaperPlanProfileMonotonicity.rank_width n N (35+k) V h
  have hp := model.monotone hw
  have hf := rank_frames W (35+k) n N h
  unfold GeneralPaperRankConstructionStorage.profile
  gcongr

theorem rank_complete (model : RationalCostModel) (W k V n N : ℕ) (h : n≤N) :
    GeneralPaperRankRecordConstructionStorage.profile model W n k V≤GeneralPaperRankRecordConstructionStorage.profile model W N k V := by
  have hw := GeneralPaperPlanProfileMonotonicity.rank_width n N (35+k) V h
  have hn := nat_word (n+1) (N+1) (Nat.add_le_add_right h 1)
  have hf := rank_frames W (35+k) n N h
  have hr := rank_record W k V n N h
  have hc := rank_partial model W k V n N h
  have hp := GeneralPaperPlanProfileMonotonicity.rank_profile model.rat model.monotone W n N k V h
  unfold GeneralPaperRankRecordConstructionStorage.profile
  gcongr

theorem cut_core (W U n N : ℕ) (h : n≤N) :
    GeneralPaperRankCutArrayStorage.coreProfile W U n≤GeneralPaperRankCutArrayStorage.coreProfile W U N := by
  have ha := native_array W (2*U) n N h
  have hw := GeneralPaperPlanProfileMonotonicity.cut_width n N (2*U) h
  unfold GeneralPaperRankCutArrayStorage.coreProfile
  gcongr

theorem shifts (model : RationalCostModel) (W U n N : ℕ) (h : n≤N) :
    GeneralPaperRankCutArrayStorage.shiftProfile model W U n≤GeneralPaperRankCutArrayStorage.shiftProfile model W U N := by
  have hc := cut_core W U n N h
  have hp := GeneralPaperPlanProfileMonotonicity.shift_profile model.rat model.monotone W n N U h
  unfold GeneralPaperRankCutArrayStorage.shiftProfile
  gcongr

theorem projected (model : RationalCostModel) (W U n N : ℕ) (h : n≤N) :
    GeneralPaperRankCutArrayStorage.projectedProfile model W U n≤GeneralPaperRankCutArrayStorage.projectedProfile model W U N := by
  have hc := cut_core W U n N h
  have hp := GeneralPaperPlanProfileMonotonicity.positions_profile model.rat model.monotone W n N U h
  unfold GeneralPaperRankCutArrayStorage.projectedProfile
  gcongr

theorem representatives (model : RationalCostModel) (W U n N : ℕ) (h : n≤N) :
    GeneralPaperRankCutArrayStorage.representativeProfile model W U n≤GeneralPaperRankCutArrayStorage.representativeProfile model W U N := by
  have hc := cut_core W U n N h
  have hp := GeneralPaperCellRepresentativePrice.profile_mono model.rat model.monotone W n N h
  unfold GeneralPaperRankCutArrayStorage.representativeProfile
  gcongr

theorem signed_cuts (model : RationalCostModel) (W U n N : ℕ) (h : n≤N) :
    GeneralPaperSignedCutStorage.profile model W n U≤GeneralPaperSignedCutStorage.profile model W N U := by
  have hw := GeneralPaperPlanProfileMonotonicity.cut_width n N U h
  have hp := GeneralPaperPlanProfileMonotonicity.cut_profile model.rat model.monotone W n N U h
  unfold GeneralPaperSignedCutStorage.profile GeneralPaperSignedCutStorage.framePeak
  gcongr

theorem tail_return (W k U n N : ℕ) (h : n≤N) :
    GeneralPaperSignedTailStorage.returnedProfile W n k U≤GeneralPaperSignedTailStorage.returnedProfile W N k U := by
  have hw := GeneralPaperPlanProfileMonotonicity.tail_width n N k U h
  unfold GeneralPaperSignedTailStorage.returnedProfile
  gcongr

theorem tail_complete (model : RationalCostModel) (W k U n N : ℕ) (h : n≤N) :
    GeneralPaperSignedTailStorage.profile model W n k U≤GeneralPaperSignedTailStorage.profile model W N k U := by
  have hw := GeneralPaperPlanProfileMonotonicity.cut_width n N U h
  have hrw := GeneralPaperPlanProfileMonotonicity.rank_width (n+1) (N+1) (35+k) (2*U) (Nat.add_le_add_right h 1)
  have htw := GeneralPaperPlanProfileMonotonicity.tail_width n N k U h
  have hr := tail_return W k U n N h
  have hc := signed_cuts model W U n N h
  have hrs := rank_partial model W k (2*U) (n+1) (N+1) (Nat.add_le_add_right h 1)
  have hp := GeneralPaperPlanProfileMonotonicity.tail_profile model.rat model.monotone W n N k U h
  unfold GeneralPaperSignedTailStorage.profile GeneralPaperSignedTailStorage.rankProfile
  gcongr

theorem cdf_return (W k U n N : ℕ) (h : n≤N) :
    GeneralPaperCDFPairConstructionStorage.returnedProfile W n k U≤GeneralPaperCDFPairConstructionStorage.returnedProfile W N k U := by
  have hw := GeneralPaperPlanProfileMonotonicity.tail_width n N k U h
  unfold GeneralPaperCDFPairConstructionStorage.returnedProfile
  gcongr

theorem cdf_complete (model : RationalCostModel) (W k U n N : ℕ) (h : n≤N) :
    GeneralPaperCDFPairConstructionStorage.profile model W n k U≤GeneralPaperCDFPairConstructionStorage.profile model W N k U := by
  have hw := GeneralPaperPlanProfileMonotonicity.cut_width n N (2*U) h
  have ht := GeneralPaperPlanProfileMonotonicity.tail_width n N k U h
  have hrr := rank_record W k U n N h
  have hcr := cdf_return W k U n N h
  have hs := shifts model W U n N h
  have hr := rank_complete model W k U n N h
  have hp := GeneralPaperPlanProfileMonotonicity.cdf_profile model.rat model.monotone W n N k U h
  unfold GeneralPaperCDFPairConstructionStorage.profile
  gcongr

theorem signed_return (W k U n N : ℕ) (h : n≤N) :
    GeneralPaperSignedUpdateConstructionStorage.returnedProfile W n k U≤GeneralPaperSignedUpdateConstructionStorage.returnedProfile W N k U := by
  have hw := GeneralPaperPlanProfileMonotonicity.tail_width n N k U h
  unfold GeneralPaperSignedUpdateConstructionStorage.returnedProfile
  gcongr

theorem signed_complete (model : RationalCostModel) (W k U n N : ℕ) (h : n≤N) :
    GeneralPaperSignedUpdateConstructionStorage.profile model W n k U≤GeneralPaperSignedUpdateConstructionStorage.profile model W N k U := by
  have hw := GeneralPaperPlanProfileMonotonicity.cut_width n N (2*U) h
  have ht := GeneralPaperPlanProfileMonotonicity.tail_width n N k U h
  have hrr := rank_record W k U n N h
  have hsr := signed_return W k U n N h
  have hproj := projected model W U n N h
  have hshift := shifts model W U n N h
  have hr := rank_complete model W k U n N h
  have hp := GeneralPaperPlanProfileMonotonicity.signed_profile model.rat model.monotone W n N k U h
  unfold GeneralPaperSignedUpdateConstructionStorage.profile
  gcongr

theorem loss_return (W k U n N : ℕ) (h : n≤N) :
    GeneralPaperQueryLossConstructionStorage.returnedProfile W n k U≤GeneralPaperQueryLossConstructionStorage.returnedProfile W N k U := by
  have hc := cdf_return W k U n N h
  have ht := tail_return W k U n N h
  have hw := GeneralPaperPlanProfileMonotonicity.tail_width n N k U h
  unfold GeneralPaperQueryLossConstructionStorage.returnedProfile
  gcongr

theorem loss_complete (model : RationalCostModel) (W k U n N : ℕ) (h : n≤N) :
    GeneralPaperQueryLossConstructionStorage.profile model W n k U≤GeneralPaperQueryLossConstructionStorage.profile model W N k U := by
  have hc := cdf_complete model W k U n N h
  have ht := tail_complete model W k U n N h
  have hcr := cdf_return W k U n N h
  have htr := tail_return W k U n N h
  have hw := GeneralPaperPlanProfileMonotonicity.tail_width n N k U h
  have hr := loss_return W k U n N h
  have hp := GeneralPaperPlanProfileMonotonicity.loss_profile model.rat model.monotone W n N k U h
  have hn := nat_word n N h
  unfold GeneralPaperQueryLossConstructionStorage.profile fields
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  gcongr

end Blotto.GeneralPaperRankStorageMonotonicity
