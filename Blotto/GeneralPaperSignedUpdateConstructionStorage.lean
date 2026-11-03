import Blotto.GeneralPaperCDFPairConstructionStorage

/-! Native signed-update preparation retains original codes, projected
positions, shifted cuts, cached ranks, all native annotation sums and the
returned plan. Empty/finished fills use the guarded rank constructor. -/
namespace Blotto.GeneralPaperSignedUpdateConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def positions {n : ℕ} (model : RationalCostModel) (W U : ℕ) (codes : FixedArrayTable n ℕ) :=
  (GeneralPaperSignedPositionsPrice.run true (fun w => w) model.rat W U codes).1

def cuts {n : ℕ} (model : RationalCostModel) (W U : ℕ) (codes : FixedArrayTable n ℕ) :=
  (GeneralPaperCDFShiftPrice.run true (fun w => w) model.rat W 1 (positions model W U codes).1).1

def ranks {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (codes : FixedArrayTable n ℕ) :=
  (GeneralPaperRankArrayExecution.prepare true (fun w => w) model.rat W k summary (cuts model W U codes).1).1

def annotationFields {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (codes : FixedArrayTable n ℕ) : ℕ :=
  let ps := (positions model W U codes).2
  let cs := (cuts model W U codes).2
  let rs := (ranks model W k U summary codes).2
  fields W [ps,cs,rs,ps+cs,ps+cs+rs,ps+cs+rs+16]

theorem annotation_fields_bound {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (codes : FixedArrayTable n ℕ) :
    annotationFields model W k U summary codes≤6*(GeneralPaperSignedTailOperands.width n k U+W)+32*W := by
  have h := GeneralPaperSignedUpdatePrice.annotation_bound true (fun w => w) model.rat W k U summary codes
  change (positions model W U codes).2+(cuts model W U codes).2+(ranks model W k U summary codes).2+16≤_ at h
  dsimp only [annotationFields]
  apply fields_bound
  intro x hx
  apply (Nat.add_le_add_left (binaryWordWidth_mono (show x≤GeneralPaperSignedTailOperands.magnitude n k from ?_)) 1).trans
    (GeneralPaperSignedTailOperands.word_bound n k U)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with hx|hx|hx|hx|hx|hx
  all_goals (rw [hx]; omega)

def returned {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (codes : FixedArrayTable n ℕ) : ℕ :=
  GeneralPaperEncodedSignedPlans.footprint W (GeneralPaperSignedUpdateExecution.run true (fun w => w) model.rat W k U summary codes).1

def returnedProfile (W n k U : ℕ) : ℕ :=
  (n*(natBits (2*U)+W)+32*W)+(n*(natBits U+W)+32*W)+
    (n*(GeneralPaperEncodedRankPlans.rankWord k+W)+32*W)+GeneralPaperSignedTailOperands.width n k U+64*W

theorem returned_bound {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (codes : FixedArrayTable n ℕ)
    (hv : ∀ i,codes.read i<2*U) : returned model W k U summary codes≤returnedProfile W n k U := by
  have hc := GeneralPaperEncodedNatArray.bounded W (natBits (2*U)) codes (fun i => Nat.add_le_add_left (binaryWordWidth_mono (hv i).le) 1)
  have hp := GeneralPaperEncodedNatArray.bounded W (natBits U) (positions model W U codes).1 (fun i =>
    Nat.add_le_add_left (binaryWordWidth_mono (GeneralPaperSignedPositionsPrice.positions true (fun w => w) model.rat W U codes hv i).le) 1)
  have hr := GeneralPaperEncodedFixedVector.rank_array W (ranks model W k U summary codes).1
  have hw := (Nat.add_le_add_left (binaryWordWidth_mono
    (GeneralPaperSignedUpdatePrice.annotation_bound true (fun w => w) model.rat W k U summary codes)) 1).trans
      (GeneralPaperSignedTailOperands.word_bound n k U)
  unfold returned returnedProfile GeneralPaperEncodedSignedPlans.footprint
  change GeneralPaperEncodedNatArray.footprint W codes+GeneralPaperEncodedNatArray.footprint W (positions model W U codes).1+
    GeneralPaperEncodedFixedVector.footprint W GeneralPaperEncodedFixedVector.rankBits (ranks model W k U summary codes).1+
    (1+binaryWordWidth _)+64*W≤_
  unfold GeneralPaperEncodedRankPlans.rankWord
  omega

def window {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (codes : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) : ℕ :=
  GeneralPaperEncodedNatArray.footprint W summary+GeneralPaperEncodedNatArray.footprint W codes+
    GeneralPaperNativeNatFillStorage.record W (positions model W U codes)+GeneralPaperNativeNatFillStorage.record W (cuts model W U codes)+
    GeneralPaperRankRecordConstructionStorage.record model W k summary (cuts model W U codes).1+
    annotationFields model W k U summary codes+returned model W k U summary codes+fields W [k,35+k,U]+
    GeneralPaperRankCutArrayStorage.projectedWindow model W U codes count hc+
    GeneralPaperRankCutArrayStorage.shiftWindow model W 1 (positions model W U codes).1 U count hc+
    GeneralPaperRankRecordConstructionStorage.window model W k summary (cuts model W U codes).1 count hc+
    (GeneralPaperSignedUpdateExecution.run true (fun w => w) model.rat W k U summary codes).2+256*W

def profile (model : RationalCostModel) (W n k U : ℕ) : ℕ :=
  ((GeneralPaperSourceParameters.prepare k).summarySize*(natBits U+W)+32*W)+(n*(natBits (2*U)+W)+32*W)+
    2*(n*(natBits (2*U)+W)+GeneralPaperSignedCutOperands.width n (2*U)+96*W)+
    GeneralPaperRankRecordConstructionStorage.recordProfile W n k U+(6*(GeneralPaperSignedTailOperands.width n k U+W)+32*W)+
    returnedProfile W n k U+fields W [k,35+k,U]+GeneralPaperRankCutArrayStorage.projectedProfile model W U n+
    GeneralPaperRankCutArrayStorage.shiftProfile model W U n+GeneralPaperRankRecordConstructionStorage.profile model W n k U+
    GeneralPaperSignedUpdatePrice.profile model.rat W n k U+256*W

theorem bounded {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (codes : FixedArrayTable n ℕ)
    (hs : ∀ i,summary.read i≤U) (hv : ∀ i,codes.read i<2*U) (count : ℕ) (hc : count≤n) :
    window model W k U summary codes count hc≤profile model W n k U := by
  have hi := GeneralPaperEncodedNatArray.bounded W (natBits U) summary (fun i => Nat.add_le_add_left (binaryWordWidth_mono (hs i)) 1)
  have hj := GeneralPaperEncodedNatArray.bounded W (natBits (2*U)) codes (fun i => Nat.add_le_add_left (binaryWordWidth_mono (hv i).le) 1)
  have hpos := GeneralPaperSignedPositionsPrice.positions true (fun w => w) model.rat W U codes hv
  have hpr := GeneralPaperNativeNatFillStorage.record_bound W U 58 (positions model W U codes)
    (fun i => (hpos i).le.trans (by omega)) (by omega) rfl
  have hcr := GeneralPaperCDFPairConstructionStorage.cut_record_bound model W U 1 (positions model W U codes).1 (Nat.le_refl _) hpos
  have hrr := GeneralPaperRankRecordConstructionStorage.record_bound model W k U summary (cuts model W U codes).1
  have ha := annotation_fields_bound model W k U summary codes
  have hr := returned_bound model W k U summary codes hv
  have hpc := GeneralPaperRankCutArrayStorage.projected_bound model W U codes hv count hc
  have hsc := GeneralPaperRankCutArrayStorage.shift_bound model W U 1 (positions model W U codes).1 (Nat.le_refl _) hpos count hc
  have hcut := GeneralPaperCDFShiftPrice.cuts true (fun w => w) model.rat W U 1 (positions model W U codes).1 (Nat.le_refl _) hpos
  have hrc := GeneralPaperRankRecordConstructionStorage.bounded model W k U summary (cuts model W U codes).1 hs hcut count hc
  have hp := GeneralPaperSignedUpdatePrice.bit_work model.rat model.monotone W k U summary codes hv hs
  change GeneralPaperNativeNatFillStorage.record W (cuts model W U codes)≤_ at hcr
  unfold window profile
  omega

end Blotto.GeneralPaperSignedUpdateConstructionStorage
