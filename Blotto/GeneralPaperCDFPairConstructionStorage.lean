import Blotto.GeneralPaperRankCutArrayStorage

/-! Native strict/weak CDF preparation retains both cut records, both rank
records, partial work sums and its full return through selected constructors.
Zero-query fills use guarded native rank windows, with no selected query. -/
namespace Blotto.GeneralPaperCDFPairConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def cuts {n : ℕ} (model : RationalCostModel) (W shift : ℕ) (queries : FixedArrayTable n ℕ) :=
  (GeneralPaperCDFShiftPrice.run true (fun w => w) model.rat W shift queries).1

def ranks {n : ℕ} (model : RationalCostModel) (W k shift : ℕ) (summary : Summary k) (queries : FixedArrayTable n ℕ) :=
  (GeneralPaperRankArrayExecution.prepare true (fun w => w) model.rat W k summary (cuts model W shift queries).1).1

theorem cut_record_bound {n : ℕ} (model : RationalCostModel) (W U shift : ℕ) (queries : FixedArrayTable n ℕ)
    (hs : shift≤1) (hq : ∀ i,queries.read i<U) :
    GeneralPaperNativeNatFillStorage.record W (cuts model W shift queries)≤
      n*(natBits (2*U)+W)+GeneralPaperSignedCutOperands.width n (2*U)+96*W :=
  GeneralPaperNativeNatFillStorage.record_bound W U 54 _
    (fun i => (GeneralPaperCDFShiftPrice.cuts true (fun w => w) model.rat W U shift queries hs hq i).trans (by omega)) (by omega) rfl

def annotationFields {n : ℕ} (model : RationalCostModel) (W k : ℕ) (summary : Summary k) (queries : FixedArrayTable n ℕ) : ℕ :=
  let lc := (cuts model W 0 queries).2
  let uc := (cuts model W 1 queries).2
  let lr := (ranks model W k 0 summary queries).2
  let ur := (ranks model W k 1 summary queries).2
  fields W [lc,uc,lr,ur,lc+uc,lc+uc+lr,lc+uc+lr+ur,lc+uc+lr+ur+16]

theorem annotation_fields_bound {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (queries : FixedArrayTable n ℕ) :
    annotationFields model W k summary queries≤8*(GeneralPaperSignedTailOperands.width n k U+W)+32*W := by
  have h := GeneralPaperCDFPairPrice.annotation_bound true (fun w => w) model.rat W k summary queries
  change (cuts model W 0 queries).2+(cuts model W 1 queries).2+(ranks model W k 0 summary queries).2+
    (ranks model W k 1 summary queries).2+16≤_ at h
  dsimp only [annotationFields]
  apply fields_bound
  intro x hx
  apply (Nat.add_le_add_left (binaryWordWidth_mono (show x≤GeneralPaperSignedTailOperands.magnitude n k from ?_)) 1).trans
    (GeneralPaperSignedTailOperands.word_bound n k U)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with hx|hx|hx|hx|hx|hx|hx|hx
  all_goals (rw [hx]; omega)

def returned {n : ℕ} (model : RationalCostModel) (W k : ℕ) (summary : Summary k) (queries : FixedArrayTable n ℕ) : ℕ :=
  GeneralPaperEncodedRankPlans.cdfFootprint W (GeneralPaperCDFPairExecution.run true (fun w => w) model.rat W k summary queries).1

def returnedProfile (W n k U : ℕ) : ℕ :=
  2*n*(GeneralPaperEncodedRankPlans.rankWord k+W)+GeneralPaperSignedTailOperands.width n k U+128*W

theorem returned_bound {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (queries : FixedArrayTable n ℕ) :
    returned model W k summary queries≤returnedProfile W n k U := by
  have hl := GeneralPaperEncodedFixedVector.rank_array W (GeneralPaperCDFPairExecution.run true (fun w => w) model.rat W k summary queries).1.lower
  have hu := GeneralPaperEncodedFixedVector.rank_array W (GeneralPaperCDFPairExecution.run true (fun w => w) model.rat W k summary queries).1.upper
  have hw := (Nat.add_le_add_left (binaryWordWidth_mono
    (GeneralPaperCDFPairPrice.annotation_bound true (fun w => w) model.rat W k summary queries)) 1).trans
      (GeneralPaperSignedTailOperands.word_bound n k U)
  have h := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hl hu) hw) (64*W)
  exact h.trans_eq (by unfold returnedProfile GeneralPaperEncodedRankPlans.rankWord; ring)

def window {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (queries : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) : ℕ :=
  GeneralPaperEncodedNatArray.footprint W summary+GeneralPaperEncodedNatArray.footprint W queries+
    GeneralPaperNativeNatFillStorage.record W (cuts model W 0 queries)+GeneralPaperNativeNatFillStorage.record W (cuts model W 1 queries)+
    GeneralPaperRankRecordConstructionStorage.record model W k summary (cuts model W 0 queries).1+
    GeneralPaperRankRecordConstructionStorage.record model W k summary (cuts model W 1 queries).1+
    annotationFields model W k summary queries+returned model W k summary queries+fields W [k,35+k,U]+
    GeneralPaperRankCutArrayStorage.shiftWindow model W 0 queries U count hc+
    GeneralPaperRankCutArrayStorage.shiftWindow model W 1 queries U count hc+
    GeneralPaperRankRecordConstructionStorage.window model W k summary (cuts model W 0 queries).1 count hc+
    GeneralPaperRankRecordConstructionStorage.window model W k summary (cuts model W 1 queries).1 count hc+
    (GeneralPaperCDFPairExecution.run true (fun w => w) model.rat W k summary queries).2+256*W

def profile (model : RationalCostModel) (W n k U : ℕ) : ℕ :=
  ((GeneralPaperSourceParameters.prepare k).summarySize*(natBits U+W)+32*W)+(n*(natBits U+W)+32*W)+
    2*(n*(natBits (2*U)+W)+GeneralPaperSignedCutOperands.width n (2*U)+96*W)+
    2*GeneralPaperRankRecordConstructionStorage.recordProfile W n k U+
    (8*(GeneralPaperSignedTailOperands.width n k U+W)+32*W)+returnedProfile W n k U+fields W [k,35+k,U]+
    2*GeneralPaperRankCutArrayStorage.shiftProfile model W U n+2*GeneralPaperRankRecordConstructionStorage.profile model W n k U+
    GeneralPaperCDFPairPrice.profile model.rat W n k U+256*W

theorem bounded {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (queries : FixedArrayTable n ℕ)
    (hs : ∀ i,summary.read i≤U) (hq : ∀ i,queries.read i<U) (count : ℕ) (hc : count≤n) :
    window model W k U summary queries count hc≤profile model W n k U := by
  have hi := GeneralPaperEncodedNatArray.bounded W (natBits U) summary (fun i => Nat.add_le_add_left (binaryWordWidth_mono (hs i)) 1)
  have hj := GeneralPaperEncodedNatArray.bounded W (natBits U) queries (fun i => Nat.add_le_add_left (binaryWordWidth_mono (hq i).le) 1)
  have hlc := cut_record_bound model W U 0 queries (by omega) hq
  have huc := cut_record_bound model W U 1 queries (Nat.le_refl _) hq
  have hlr := GeneralPaperRankRecordConstructionStorage.record_bound model W k U summary (cuts model W 0 queries).1
  have hur := GeneralPaperRankRecordConstructionStorage.record_bound model W k U summary (cuts model W 1 queries).1
  have ha := annotation_fields_bound model W k U summary queries
  have hr := returned_bound model W k U summary queries
  have hls := GeneralPaperRankCutArrayStorage.shift_bound model W U 0 queries (by omega) hq count hc
  have hus := GeneralPaperRankCutArrayStorage.shift_bound model W U 1 queries (Nat.le_refl _) hq count hc
  have hrl := GeneralPaperRankRecordConstructionStorage.bounded model W k U summary (cuts model W 0 queries).1 hs
    (GeneralPaperCDFShiftPrice.cuts true (fun w => w) model.rat W U 0 queries (by omega) hq) count hc
  have hru := GeneralPaperRankRecordConstructionStorage.bounded model W k U summary (cuts model W 1 queries).1 hs
    (GeneralPaperCDFShiftPrice.cuts true (fun w => w) model.rat W U 1 queries (Nat.le_refl _) hq) count hc
  have hw := GeneralPaperCDFPairPrice.bit_work model.rat model.monotone W k U summary queries hq hs
  unfold window profile
  omega

end Blotto.GeneralPaperCDFPairConstructionStorage
