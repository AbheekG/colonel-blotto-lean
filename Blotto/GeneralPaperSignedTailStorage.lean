import Blotto.GeneralPaperSignedCutStorage
import Blotto.GeneralPaperRankConstructionStorage

/-! Both native cut arrays, both native rank records and every intermediate
annotation coexist with one selected cut/rank constructor. Finite rank types
and the actual final annotation derive all retained payload caps. -/
namespace Blotto.GeneralPaperSignedTailStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def cuts {n : ℕ} (model : RationalCostModel) (W U : ℕ) (negative : Bool) (queries : FixedArrayTable n ℕ) :=
  (GeneralPaperSignedCutExecution.run true (fun w => w) model.rat W U negative queries).1

def ranks {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k)
    (negative : Bool) (queries : FixedArrayTable n ℕ) :=
  (GeneralPaperRankArrayExecution.prepare true (fun w => w) model.rat W k summary (cuts model W U negative queries).1).1

def rankReturned {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k)
    (negative : Bool) (queries : FixedArrayTable n ℕ) : ℕ :=
  GeneralPaperEncodedFixedVector.footprint W GeneralPaperEncodedFixedVector.rankBits (ranks model W k U summary negative queries).1+
    natBits (ranks model W k U summary negative queries).2+64*W

def rankProfile (W n k U : ℕ) : ℕ :=
  (n+1)*(GeneralPaperEncodedRankPlans.rankWord k+W)+GeneralPaperRankArrayOperands.width (n+1) (35+k) (2*U)+96*W

theorem rank_returned_bound {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k)
    (negative : Bool) (queries : FixedArrayTable n ℕ) : rankReturned model W k U summary negative queries≤rankProfile W n k U := by
  have hr := GeneralPaperEncodedFixedVector.rank_array W (ranks model W k U summary negative queries).1
  have ha := GeneralPaperRankConstructionStorage.annotation true (fun w => w) model.rat W k (2*U) summary
    (cuts model W U negative queries).1 (n+1) (Nat.le_refl _)
  change natBits (ranks model W k U summary negative queries).2≤_ at ha
  unfold rankReturned rankProfile GeneralPaperEncodedRankPlans.rankWord
  omega

def annotationFields {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k)
    (queries : FixedArrayTable n ℕ) : ℕ :=
  let pc := (cuts model W U false queries).2
  let nc := (cuts model W U true queries).2
  let pr := (ranks model W k U summary false queries).2
  let nr := (ranks model W k U summary true queries).2
  fields W [pc,nc,pr,nr,pc+nc,pc+nc+pr,pc+nc+pr+nr,pc+nc+pr+nr+16]

theorem annotation_fields_bound {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k)
    (queries : FixedArrayTable n ℕ) :
    annotationFields model W k U summary queries≤8*(GeneralPaperSignedTailOperands.width n k U+W)+32*W := by
  have h := GeneralPaperSignedTailOperands.annotation_bound true (fun w => w) model.rat W k U summary queries
  change (cuts model W U false queries).2+(cuts model W U true queries).2+
    (ranks model W k U summary false queries).2+(ranks model W k U summary true queries).2+16≤_ at h
  dsimp only [annotationFields]
  apply fields_bound
  intro x hx
  apply (Nat.add_le_add_left (binaryWordWidth_mono (show x≤GeneralPaperSignedTailOperands.magnitude n k from ?_)) 1).trans
    (GeneralPaperSignedTailOperands.word_bound n k U)
  simp only [List.mem_cons] at hx
  rcases hx with hx|hx|hx|hx|hx|hx|hx|hx|hx
  all_goals first | (cases hx; done) | (rw [hx]; omega)

def returned {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (queries : FixedArrayTable n ℕ) : ℕ :=
  GeneralPaperEncodedRankPlans.tailFootprint W (GeneralPaperSignedTailExecution.run true (fun w => w) model.rat W k U summary queries).1

def returnedProfile (W n k U : ℕ) : ℕ :=
  2*(n+1)*(GeneralPaperEncodedRankPlans.rankWord k+W)+GeneralPaperSignedTailOperands.width n k U+128*W

theorem returned_bound {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (queries : FixedArrayTable n ℕ) :
    returned model W k U summary queries≤returnedProfile W n k U := by
  have hp := GeneralPaperEncodedFixedVector.rank_array W
    (GeneralPaperSignedTailExecution.run true (fun w => w) model.rat W k U summary queries).1.positive
  have hn := GeneralPaperEncodedFixedVector.rank_array W
    (GeneralPaperSignedTailExecution.run true (fun w => w) model.rat W k U summary queries).1.negative
  have hw := (Nat.add_le_add_left (binaryWordWidth_mono
    (GeneralPaperSignedTailOperands.annotation_bound true (fun w => w) model.rat W k U summary queries)) 1).trans
      (GeneralPaperSignedTailOperands.word_bound n k U)
  have h := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hp hn) hw) (64*W)
  exact h.trans_eq (by unfold returnedProfile GeneralPaperEncodedRankPlans.rankWord; ring)

def window {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (queries : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n+1) (q : Fin (n+1)) : ℕ :=
  GeneralPaperEncodedNatArray.footprint W summary+GeneralPaperEncodedNatArray.footprint W queries+
    GeneralPaperSignedCutStorage.returned model W U false queries+GeneralPaperSignedCutStorage.returned model W U true queries+
    rankReturned model W k U summary false queries+rankReturned model W k U summary true queries+
    annotationFields model W k U summary queries+fields W [k,35+k,U,2*U]+
    returned model W k U summary queries+
    GeneralPaperSignedCutStorage.window model W U false queries count hc q+
    GeneralPaperSignedCutStorage.window model W U true queries count hc q+
    GeneralPaperRankConstructionStorage.window model (fun w => w) W k summary (cuts model W U false queries).1 count hc q+
    GeneralPaperRankConstructionStorage.window model (fun w => w) W k summary (cuts model W U true queries).1 count hc q+
    (GeneralPaperSignedTailExecution.run true (fun w => w) model.rat W k U summary queries).2+256*W

def profile (model : RationalCostModel) (W n k U : ℕ) : ℕ :=
  ((GeneralPaperSourceParameters.prepare k).summarySize*(natBits (2*U)+W)+32*W)+(n*(natBits U+W)+32*W)+
    2*((n+1)*(natBits (2*U)+W)+GeneralPaperSignedCutOperands.width n U+96*W)+2*rankProfile W n k U+
    (8*(GeneralPaperSignedTailOperands.width n k U+W)+32*W)+fields W [k,35+k,U,2*U]+
    returnedProfile W n k U+2*GeneralPaperSignedCutStorage.profile model W n U+
    2*GeneralPaperRankConstructionStorage.profile model W (n+1) k (2*U)+GeneralPaperSignedTailPrice.profile model.rat W n k U+256*W

theorem bounded {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (queries : FixedArrayTable n ℕ)
    (hs : ∀ r,summary.read r≤2*U) (hq : ∀ q,queries.read q≤U)
    (count : ℕ) (hc : count≤n+1) (q : Fin (n+1)) : window model W k U summary queries count hc q≤profile model W n k U := by
  have hi := GeneralPaperEncodedNatArray.bounded W (natBits (2*U)) summary (fun r => Nat.add_le_add_left (binaryWordWidth_mono (hs r)) 1)
  have hq' := GeneralPaperEncodedNatArray.bounded W (natBits U) queries (fun q => Nat.add_le_add_left (binaryWordWidth_mono (hq q)) 1)
  have hp := GeneralPaperSignedCutStorage.returned_bound model W U false queries hq
  have hn := GeneralPaperSignedCutStorage.returned_bound model W U true queries hq
  have hpr := rank_returned_bound model W k U summary false queries
  have hnr := rank_returned_bound model W k U summary true queries
  have ha := annotation_fields_bound model W k U summary queries
  have hr := returned_bound model W k U summary queries
  have hpc := GeneralPaperSignedCutStorage.bounded model W U false queries hq count hc q
  have hnc := GeneralPaperSignedCutStorage.bounded model W U true queries hq count hc q
  have hprs := GeneralPaperRankConstructionStorage.bounded model (fun w => w) W k (2*U) summary
    (cuts model W U false queries).1 count hc q (GeneralPaperSignedCutPrice.codes true (fun w => w) model.rat W U false queries hq) hs
  have hnrs := GeneralPaperRankConstructionStorage.bounded model (fun w => w) W k (2*U) summary
    (cuts model W U true queries).1 count hc q (GeneralPaperSignedCutPrice.codes true (fun w => w) model.rat W U true queries hq) hs
  have hw := GeneralPaperSignedTailPrice.bit_work model.rat model.monotone W k U summary queries hq hs
  unfold window profile
  omega

end Blotto.GeneralPaperSignedTailStorage
