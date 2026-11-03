import Blotto.GeneralPaperEqualFullBitOutput
import Blotto.GeneralPaperEncodedBasisStorage

/-! Complete encoded ownership of the actual equal-budget returned sampler.
Proof indices and certificates erase. All runtime data fields, tags, labels,
array/list references and descriptors are counted; the budget is owned once.
These are erased observers, not additional preparation traversals. -/
namespace Blotto.GeneralPaperEqualRetainedStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperEqualPreparedCache (Prepared)
open GeneralPaperEqualBooleanCache (Cache)
open GeneralPaperPositiveSegmentCompaction (count compact)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 900000

def routeFoot {m : ℕ} (W : ℕ) (r : GroupRoute m) : ℕ :=
  (match r.1 with | none => 1 | some g => 1 + natBits g.val) + rationalWordWidth r.2 + 16 * W

theorem route_bound {m c : ℕ} (W : ℕ) (r : GroupRoute m) (h : RationalHeight r.2 c) :
    routeFoot W r ≤ 4 + binaryWordWidth m + 2 * c + 16 * W := by
  have hr := rationalWordWidth_of_height h
  unfold routeFoot
  split
  · omega
  · rename_i g hg
    have hi := binaryWordWidth_mono (Nat.le_of_lt g.isLt)
    have ht : 1 + natBits g.val ≤ 2 + binaryWordWidth m := by
      change 1 + (1 + binaryWordWidth g.val) ≤ _
      omega
    exact (Nat.add_le_add_right (Nat.add_le_add ht hr) (16 * W)).trans (by omega)

def segmentFoot {m r : ℕ} {l : RationalSegmentLottery m r} (W : ℕ)
    (p : PreparedSegmentDescriptor l) : ℕ :=
  arrayFootprint W rationalWordWidth p.weights +
    arrayFootprint W (arrayFootprint W rationalWordWidth) p.left +
    arrayFootprint W (arrayFootprint W rationalWordWidth) p.right + 32 * W

def segmentProfile (W m r s : ℕ) : ℕ :=
  arrayProfile W r (1 + 2 * s) +
    2 * arrayProfile W r (arrayProfile W m (1 + 2 * s)) + 32 * W

theorem segment_bound {m r s : ℕ} {l : RationalSegmentLottery m r} (W : ℕ)
    (p : PreparedSegmentDescriptor l) (h : l.HeightAt s) : segmentFoot W p ≤ segmentProfile W m r s := by
  have hw := array_bound W (1 + 2 * s) rationalWordWidth p.weights (fun i => by
    rw [p.weight_correct]; exact rationalWordWidth_of_height (h.1 i))
  have hp := array_bound W (arrayProfile W m (1 + 2 * s)) (arrayFootprint W rationalWordWidth) p.left
    (fun i => array_bound W (1 + 2 * s) rationalWordWidth (p.left.read i) (fun j => by
      rw [p.left_correct]; exact rationalWordWidth_of_height (h.2 i j).1))
  have hq := array_bound W (arrayProfile W m (1 + 2 * s)) (arrayFootprint W rationalWordWidth) p.right
    (fun i => array_bound W (1 + 2 * s) rationalWordWidth (p.right.read i) (fun j => by
      rw [p.right_correct]; exact rationalWordWidth_of_height (h.2 i j).2))
  unfold segmentFoot segmentProfile
  omega

def preparedFoot {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (W : ℕ) (p : Prepared G l) : ℕ :=
  arrayFootprint W (routeFoot W) p.routes.table + segmentFoot W p.segments +
    arrayFootprint W natBits p.counts + fields W [p.D, p.rangeBits, p.midpointBits, p.midpointCount] +
    rationalWordWidth p.budget + 64 * W

def preparedProfile (W n m r s c d P b : ℕ) : ℕ :=
  arrayProfile W n (4 + binaryWordWidth m + 2 * c + 16 * W) + segmentProfile W m r s +
    arrayProfile W r (1 + d) + 4 * (P + W) + 32 * W + b + 64 * W

theorem prepared_bound {n m k s c d P : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (W : ℕ) (p : Prepared G l) (hl : l.HeightAt s)
    (hc : ∀ j, RationalHeight (p.routes.table.read j).2 c)
    (hd : ∀ i, binaryWordWidth (p.counts.read i) ≤ d)
    (hp : ∀ x ∈ [p.D, p.rangeBits, p.midpointBits, p.midpointCount], natBits x ≤ P) :
    preparedFoot W p ≤ preparedProfile W n m (count l) s c d P (rationalWordWidth p.budget) := by
  have hr := array_bound W (4 + binaryWordWidth m + 2 * c + 16 * W) (routeFoot W) p.routes.table
    (fun j => route_bound W _ (hc j))
  have hs := segment_bound W p.segments (GeneralPaperPositiveSegmentCompaction.compact_height l hl)
  have hn := array_bound W (1 + d) natBits p.counts (fun i => Nat.add_le_add_left (hd i) 1)
  have hm := fields_bound W P [p.D, p.rangeBits, p.midpointBits, p.midpointCount] hp
  simp only [List.length_cons, List.length_nil] at hm
  unfold preparedFoot preparedProfile
  omega

def wordFoot {w : ℕ} (W : ℕ) (a : FixedBinaryWord w) : ℕ :=
  listFootprint W (fun _ : Bool => 1) a.bits + 16 * W

def wordProfile (W w : ℕ) : ℕ := w * (1 + 2 * W) + 48 * W

theorem word_bound {w : ℕ} (W : ℕ) (a : FixedBinaryWord w) : wordFoot W a ≤ wordProfile W w := by
  have h := list_bound W 1 (fun _ : Bool => 1) a.bits (fun _ _ => le_rfl)
  rw [a.size] at h
  unfold wordFoot wordProfile
  omega

def cacheFoot {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (W : ℕ) (c : Cache p) : ℕ :=
  wordFoot W c.denominator +
    listFootprint W (fun row => natBits row.1.val + wordFoot W row.2 + 16 * W) c.rows +
    listFootprint W (fun _ : Unit => 0) c.ruler + 64 * W

def cacheProfile (W r w : ℕ) : ℕ :=
  wordProfile W (w + 1) +
    r * (1 + binaryWordWidth r + wordProfile W (w + 1) + 18 * W) + 32 * W +
    w * (2 * W) + 32 * W + 64 * W

theorem cache_bound {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (W : ℕ) (c : Cache p) : cacheFoot W c ≤ cacheProfile W (count l) p.rangeBits := by
  have hd := word_bound W c.denominator
  have hr := list_bound W (1 + binaryWordWidth (count l) + wordProfile W (p.rangeBits + 1) + 16 * W)
    (fun row => natBits row.1.val + wordFoot W row.2 + 16 * W) c.rows (by
      intro row _
      have hi := binaryWordWidth_mono (Nat.le_of_lt row.1.isLt)
      have hw := word_bound W row.2
      unfold natBits
      omega)
  rw [GeneralPaperEqualBooleanCache.rows_length] at hr
  have hu := list_bound W 0 (fun _ : Unit => 0) c.ruler (fun _ _ => le_rfl)
  rw [c.ruler_length] at hu
  unfold cacheFoot cacheProfile
  nlinarith only [hd, hr, hu]

def footprint {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (W : ℕ) (s : GeneralPaperEqualStoredBitSampler.Sampler G l) : ℕ :=
  preparedFoot W s.prepared + cacheFoot W s.categorical + fields W [s.exponent, s.address] + 64 * W

theorem stored_bound {n m k s c d P : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (W : ℕ) (a : GeneralPaperEqualStoredBitSampler.Sampler G l) (hl : l.HeightAt s)
    (hc : ∀ j, RationalHeight (a.prepared.routes.table.read j).2 c)
    (hd : ∀ i, binaryWordWidth (a.prepared.counts.read i) ≤ d)
    (hp : ∀ x ∈ [a.prepared.D, a.prepared.rangeBits, a.prepared.midpointBits, a.prepared.midpointCount], natBits x ≤ P) :
    footprint W a ≤ preparedProfile W n m (count l) s c d P (rationalWordWidth a.prepared.budget) +
      cacheProfile W (count l) a.prepared.rangeBits + natBits a.exponent + natBits a.address + 98 * W := by
  have h := prepared_bound W a.prepared hl hc hd hp
  have hCache := cache_bound W a.categorical
  unfold footprint fields
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
  omega

end Blotto.GeneralPaperEqualRetainedStorage
