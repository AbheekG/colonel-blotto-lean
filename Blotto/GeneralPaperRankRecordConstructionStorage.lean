import Blotto.GeneralPaperActualFieldPartitionStorage

/-! Complete native cached-rank records and guarded callbacks. Empty fills
and the final prefix retain buffers, native work and frames without choosing
a nonexistent query. Every active query is the actual next fill index. -/
namespace Blotto.GeneralPaperRankRecordConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def record {n : ℕ} (model : RationalCostModel) (W k : ℕ) (summary : Summary k) (cuts : FixedArrayTable n ℕ) : ℕ :=
  let r := (GeneralPaperRankArrayExecution.prepare true (fun w => w) model.rat W k summary cuts).1
  GeneralPaperEncodedFixedVector.footprint W GeneralPaperEncodedFixedVector.rankBits r.1+natBits r.2+64*W

def recordProfile (W n k V : ℕ) : ℕ :=
  n*(GeneralPaperEncodedRankPlans.rankWord k+W)+GeneralPaperRankArrayOperands.width n (35+k) V+96*W

theorem record_bound {n : ℕ} (model : RationalCostModel) (W k V : ℕ) (summary : Summary k) (cuts : FixedArrayTable n ℕ) :
    record model W k summary cuts≤recordProfile W n k V := by
  have hr := GeneralPaperEncodedFixedVector.rank_array W
    (GeneralPaperRankArrayExecution.prepare true (fun w => w) model.rat W k summary cuts).1.1
  have ha := GeneralPaperRankConstructionStorage.annotation true (fun w => w) model.rat W k V summary cuts n (Nat.le_refl _)
  change natBits (GeneralPaperRankArrayExecution.prepare true (fun w => w) model.rat W k summary cuts).1.2≤_ at ha
  dsimp only [record,recordProfile,GeneralPaperEncodedRankPlans.rankWord]
  omega

def callback {n : ℕ} (model : RationalCostModel) (W k : ℕ) (summary : Summary k) (cuts : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) : ℕ :=
  if h : count<n then GeneralPaperRankConstructionStorage.window model (fun w => w) W k summary cuts count hc ⟨count,h⟩ else 0

theorem callback_bound {n : ℕ} (model : RationalCostModel) (W k V : ℕ) (summary : Summary k) (cuts : FixedArrayTable n ℕ)
    (hs : ∀ i,summary.read i≤V) (hcCode : ∀ i,cuts.read i≤V) (count : ℕ) (hc : count≤n) :
    callback model W k summary cuts count hc≤GeneralPaperRankConstructionStorage.profile model W n k V := by
  unfold callback
  split
  · exact GeneralPaperRankConstructionStorage.bounded model (fun w => w) W k V summary cuts count hc _ hcCode hs
  · exact Nat.zero_le _

def window {n : ℕ} (model : RationalCostModel) (W k : ℕ) (summary : Summary k) (cuts : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) : ℕ :=
  2*GeneralPaperRankConstructionStorage.buffer true (fun w => w) model.rat W k (35+k) summary cuts count hc+
    2*natBits (GeneralPaperRankArrayExecution.fill true (fun w => w) model.rat W k (35+k) summary cuts count hc).1.2+
    GeneralPaperRankConstructionStorage.frames W n (35+k)+record model W k summary cuts+
    fields W [35,k,35+k,n,count,count+1]+callback model W k summary cuts count hc+
    (GeneralPaperRankArrayExecution.prepare true (fun w => w) model.rat W k summary cuts).2+256*W

def profile (model : RationalCostModel) (W n k V : ℕ) : ℕ :=
  2*(n*(natBits (GeneralPaperSourceParameters.prepare k).summarySize+W)+64*W)+
    2*GeneralPaperRankArrayOperands.width n (35+k) V+GeneralPaperRankConstructionStorage.frames W n (35+k)+
    recordProfile W n k V+6*(natBits (35+k)+natBits (n+1)+W)+32*W+
    GeneralPaperRankConstructionStorage.profile model W n k V+GeneralPaperRankArrayPrice.profile model.rat W n k V+256*W

theorem bounded {n : ℕ} (model : RationalCostModel) (W k V : ℕ) (summary : Summary k) (cuts : FixedArrayTable n ℕ)
    (hs : ∀ i,summary.read i≤V) (hcCode : ∀ i,cuts.read i≤V) (count : ℕ) (hc : count≤n) :
    window model W k summary cuts count hc≤profile model W n k V := by
  have hb := GeneralPaperRankConstructionStorage.buffer_bound true (fun w => w) model.rat W k (35+k) summary cuts count hc
  have ha := GeneralPaperRankConstructionStorage.annotation true (fun w => w) model.rat W k V summary cuts count hc
  have hr := record_bound model W k V summary cuts
  have hcb := callback_bound model W k V summary cuts hs hcCode count hc
  have hp := GeneralPaperRankArrayPrice.bit_work model.rat model.monotone W k V summary cuts hcCode hs
  have hf := fields_bound W (natBits (35+k)+natBits (n+1)) [35,k,35+k,n,count,count+1] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with hx|hx|hx|hx|hx|hx
    all_goals first
    | (rw [hx]; exact (Nat.add_le_add_left (binaryWordWidth_mono (show _≤35+k by omega)) 1).trans (Nat.le_add_right _ _))
    | (rw [hx]; exact (Nat.add_le_add_left (binaryWordWidth_mono (show _≤n+1 by omega)) 1).trans (Nat.le_add_left _ _)))
  change fields W [35,k,35+k,n,count,count+1]≤6*(natBits (35+k)+natBits (n+1)+W)+32*W at hf
  unfold window profile
  omega

end Blotto.GeneralPaperRankRecordConstructionStorage
