import Blotto.GeneralPaperRankTraversalStorage
import Blotto.GeneralPaperEncodedReferenceVector

/-! Cached-rank construction counts full reserved output arrays, native
work annotations, recursion controls and one selected lookup. Summary and
cut payloads are borrowed from the already-retained cache/summary buffers.
The code cap V remains explicit until its actual caller supplies it. -/
namespace Blotto.GeneralPaperRankConstructionStorage
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperEncodedScalarStorage GeneralPaperRankArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def selectedBits {k : ℕ} (W : ℕ) (r : GeneralPaperSelectedRank.Lookup k) : ℕ :=
  natBits r.position.val+natBits r.work+natBits r.probes+64*W

theorem selected_bound (bits : Bool) (primitive : ℕ → ℕ) (W k V : ℕ) (values : Summary k) (cut : ℕ) :
    selectedBits W (GeneralPaperSelectedRankPrice.run bits primitive W k (35+k) values cut).1≤
      3*GeneralPaperRankOperands.width (35+k) V+64*W := by
  rw [GeneralPaperSelectedRankPrice.data bits primitive W k (35+k) values cut rfl]
  have h := GeneralPaperRankTraversalStorage.lookup_bound false (fun _ => 1) W (35+k) V values cut
    (GeneralPaperSelectedRank.selected_size k)
  rw [GeneralPaperRankLookupPrice.data false (fun _ => 1) W (35+k) values cut (GeneralPaperSelectedRank.selected_size k)] at h
  exact h

def query (model : RationalCostModel) (W k : ℕ) (values : Summary k) (cut : ℕ) : ℕ :=
  GeneralPaperRankTraversalStorage.peak W values cut (35+k) (35+k) 0 (GeneralPaperSourceParameters.prepare k).summarySize+
    selectedBits W (GeneralPaperSelectedRankPrice.run true model.rat W k (35+k) values cut).1+
    (GeneralPaperSelectedRankPrice.run true model.rat W k (35+k) values cut).2+256*W

def queryProfile (model : RationalCostModel) (W k V : ℕ) : ℕ :=
  let d := 35+k
  let L := GeneralPaperRankOperands.width d V
  (d+1)*(32*L+512*W)+3*L+64*W+2048*(d+1)*(W+model.rat L)+256*W

theorem query_bound (model : RationalCostModel) (W k V : ℕ) (values : Summary k) (cut : ℕ)
    (hc : cut≤V) (hv : ∀ i,values.read i≤V) : query model W k values cut≤queryProfile model W k V := by
  have hs := GeneralPaperRankTraversalStorage.bounded W (35+k) V (35+k) 0 _ cut values (Nat.le_refl _)
    (Nat.zero_le _) (Nat.le_refl _) (GeneralPaperSelectedRank.selected_size k) hc hv
  have ho := selected_bound true model.rat W k V values cut
  have hw := GeneralPaperSelectedRankPrice.bit_work model.rat model.monotone W k (35+k) V values cut rfl hc hv
  exact (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hs ho) hw) (256*W)).trans_eq (by unfold queryProfile; ring)

def buffer {n : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k depth : ℕ) (values : Summary k)
    (cuts : FixedArrayTable n ℕ) (count : ℕ) (hc : count≤n) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W n (fun r => natBits r.val)
    (fill bits index primitive W k depth values cuts count hc).1.1

theorem buffer_bound {n : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k depth : ℕ) (values : Summary k)
    (cuts : FixedArrayTable n ℕ) (count : ℕ) (hc : count≤n) :
    buffer bits index primitive W k depth values cuts count hc≤
      n*(natBits (GeneralPaperSourceParameters.prepare k).summarySize+W)+64*W := by
  apply GeneralPaperEncodedReferenceVector.reserved_bound W _ n _ _
  · rw [fill_size]; exact hc
  · intro i
    apply Nat.add_le_add_left
    apply binaryWordWidth_mono
    exact Nat.le_of_lt_succ ((fill bits index primitive W k depth values cuts count hc).1.1[i.val]).isLt

theorem annotation {n : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k V : ℕ) (values : Summary k)
    (cuts : FixedArrayTable n ℕ) (count : ℕ) (hc : count≤n) :
    natBits (fill bits index primitive W k (35+k) values cuts count hc).1.2≤
      GeneralPaperRankArrayOperands.width n (35+k) V := by
  have h := (GeneralPaperRankArrayOperands.fill_annotation bits index primitive W k (35+k) values cuts rfl count hc).trans
    (GeneralPaperRankArrayOperands.annotation_cap n (35+k) count hc)
  exact (Nat.add_le_add_left (binaryWordWidth_mono h) 1).trans (GeneralPaperRankArrayOperands.word_bound n (35+k) V)

def frames (W n depth : ℕ) : ℕ := (n+1)*(4*natBits (n+1)+4*natBits depth+128*W)

def window {n : ℕ} (model : RationalCostModel) (index : ℕ → ℕ) (W k : ℕ) (values : Summary k)
    (cuts : FixedArrayTable n ℕ) (count : ℕ) (hc : count≤n) (q : Fin n) : ℕ :=
  2*buffer true index model.rat W k (35+k) values cuts count hc+
    2*natBits (fill true index model.rat W k (35+k) values cuts count hc).1.2+
    frames W n (35+k)+query model W k values (cuts.read q)+
    4*model.rat (GeneralPaperRankArrayOperands.width n (35+k) (cuts.read q))+256*W

def profile (model : RationalCostModel) (W n k V : ℕ) : ℕ :=
  2*(n*(natBits (GeneralPaperSourceParameters.prepare k).summarySize+W)+64*W)+
    2*GeneralPaperRankArrayOperands.width n (35+k) V+frames W n (35+k)+queryProfile model W k V+
    4*model.rat (GeneralPaperRankArrayOperands.width n (35+k) V)+256*W

theorem bounded {n : ℕ} (model : RationalCostModel) (index : ℕ → ℕ) (W k V : ℕ)
    (values : Summary k) (cuts : FixedArrayTable n ℕ) (count : ℕ) (hc : count≤n) (q : Fin n)
    (hCuts : ∀ q,cuts.read q≤V) (hValues : ∀ i,values.read i≤V) :
    window model index W k values cuts count hc q≤profile model W n k V := by
  have hb := buffer_bound true index model.rat W k (35+k) values cuts count hc
  have ha := annotation true index model.rat W k V values cuts count hc
  have hq := query_bound model W k V values (cuts.read q) (hCuts q) hValues
  have hWidth : GeneralPaperRankArrayOperands.width n (35+k) (cuts.read q)≤GeneralPaperRankArrayOperands.width n (35+k) V := by
    have h := binaryWordWidth_mono (Nat.add_le_add_right (hCuts q) 1)
    unfold GeneralPaperRankArrayOperands.width GeneralPaperRankOperands.width
    omega
  have hp := model.monotone hWidth
  unfold window profile
  omega

end Blotto.GeneralPaperRankConstructionStorage
