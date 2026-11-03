import Blotto.GeneralPaperEqualPreparedCopyLifetime

/-! Complete grouped retained-sampler copy: original and copied owners,
prepared and Boolean child windows, precision/address scalar scratch and
actual parent work/partial-sum/control fields. -/
namespace Blotto.GeneralPaperEqualSamplerCopyLifetime
open GeneralPaperEncodedScalarStorage GeneralPaperEqualRetainedStorage
open GeneralPaperPositiveSegmentCompaction (compact count)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def ownerProfile (W n m r s c d P b w e a : ℕ) : ℕ :=
  preparedProfile W n m r s c d P b + cacheProfile W r w + natBits e + natBits a + 98 * W

theorem owner {n m r s c d P : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (W : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) (hl : (compact l).HeightAt s)
    (hc : ∀ j,RationalHeight (source.prepared.routes.table.read j).2 c)
    (hd : ∀ i,binaryWordWidth (source.prepared.counts.read i) ≤ d)
    (hp : ∀ x ∈ [source.prepared.D,source.prepared.rangeBits,source.prepared.midpointBits,source.prepared.midpointCount],natBits x ≤ P) :
    footprint W source ≤ ownerProfile W n m (count l) s c d P (rationalWordWidth source.prepared.budget)
      source.prepared.rangeBits source.exponent source.address := by
  have hPrepared := GeneralPaperEqualPreparedCopyLifetime.owner W source.prepared hl hc hd hp
  have hBoolean := cache_bound W source.categorical
  unfold footprint fields ownerProfile
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  omega

def controls {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) : List ℕ :=
  let prepared := (GeneralPaperEqualPreparedCopy.run S A source.prepared).2
  let boolean := (GeneralPaperEqualBooleanCopy.run S A source.categorical).2
  let exponent := natBits source.exponent + 32 * (S + A + 1)
  let address := natBits source.address + 32 * (S + A + 1)
  [n,m,count l,S,A,source.exponent,source.address,prepared,boolean,exponent,address,
    prepared+boolean,prepared+boolean+exponent,prepared+boolean+exponent+address,
    (GeneralPaperEqualSamplerCopy.run S A source).2]

def parentCap (S A n m r s c d P b w e a : ℕ) : ℕ :=
  GeneralPaperEqualSamplerCopy.price S A n m r s c d P b w e a + n + m + r + S + A + e + a

def window {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (q : ℕ) (hq : q ≤ n) (i : ℕ) (hi : i ≤ count l) (j : ℕ) (hj : j ≤ m)
    (current : Option {x : Fin (count l) × FixedBinaryWord (source.prepared.rangeBits + 1) // x ∈ source.categorical.rows}) : ℕ :=
  footprint S source + footprint A (GeneralPaperEqualSamplerCopy.run S A source).1 +
    GeneralPaperEqualPreparedCopyLifetime.window S A source.prepared q hq i hi j hj +
    GeneralPaperEqualBooleanCopyLifetime.window S A source.categorical current +
    GeneralPaperScalarTableCopyLifetime.scalarWindow S A natBits source.exponent +
    GeneralPaperScalarTableCopyLifetime.scalarWindow S A natBits source.address +
    fields S (controls S A source) + 256 * (S + A + 1)

def profile (S A n m r s c d P b w e a : ℕ) : ℕ :=
  ownerProfile S n m r s c d P b w e a + ownerProfile A n m r s c d P b w e a +
    GeneralPaperEqualPreparedCopyLifetime.profile S A n m r s c d P b +
    GeneralPaperEqualBooleanCopyLifetime.profile S A r w +
    GeneralPaperScalarTableCopyLifetime.scalarProfile S A (natBits e) +
    GeneralPaperScalarTableCopyLifetime.scalarProfile S A (natBits a) +
    15 * (natBits (parentCap S A n m r s c d P b w e a) + S) + 32 * S + 256 * (S + A + 1)

theorem all_cursors {n m r s c d P : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) (hl : (compact l).HeightAt s)
    (hc : ∀ j,RationalHeight (source.prepared.routes.table.read j).2 c)
    (hd : ∀ i,binaryWordWidth (source.prepared.counts.read i) ≤ d)
    (hp : ∀ x ∈ [source.prepared.D,source.prepared.rangeBits,source.prepared.midpointBits,source.prepared.midpointCount],natBits x ≤ P)
    (hA : 1 ≤ A) (hIndexN : binaryWordWidth (n + 1) ≤ A)
    (hIndexM : binaryWordWidth (m + 1) ≤ A) (hIndexR : binaryWordWidth (count l + 1) ≤ A)
    (q : ℕ) (hq : q ≤ n) (i : ℕ) (hi : i ≤ count l) (j : ℕ) (hj : j ≤ m)
    (current : Option {x : Fin (count l) × FixedBinaryWord (source.prepared.rangeBits + 1) // x ∈ source.categorical.rows}) :
    window S A source q hq i hi j hj current ≤ profile S A n m (count l) s c d P
      (rationalWordWidth source.prepared.budget) source.prepared.rangeBits source.exponent source.address := by
  have hSource := owner S source hl hc hd hp
  have hTarget : footprint A (GeneralPaperEqualSamplerCopy.run S A source).1 ≤
      ownerProfile A n m (count l) s c d P (rationalWordWidth source.prepared.budget)
        source.prepared.rangeBits source.exponent source.address := by
    rw [GeneralPaperEqualSamplerCopy.data]
    exact owner A source hl hc hd hp
  have hPrepared := GeneralPaperEqualPreparedCopyLifetime.all_cursors S A source.prepared hl hc hd hp
    hA hIndexN hIndexM hIndexR q hq i hi j hj
  have hBoolean := GeneralPaperEqualBooleanCopyLifetime.bounded S A source.categorical current
  have hExponent := GeneralPaperScalarTableCopyLifetime.scalar_bound S A (natBits source.exponent) natBits source.exponent le_rfl
  have hAddress := GeneralPaperScalarTableCopyLifetime.scalar_bound S A (natBits source.address) natBits source.address le_rfl
  have hWork := GeneralPaperEqualSamplerCopy.work S A source hl hc hd hp
  have hReturn : (GeneralPaperEqualSamplerCopy.run S A source).2 =
      (GeneralPaperEqualPreparedCopy.run S A source.prepared).2 + (GeneralPaperEqualBooleanCopy.run S A source.categorical).2 +
      (natBits source.exponent + 32 * (S + A + 1)) + (natBits source.address + 32 * (S + A + 1)) +
      128 * (S + A + 1) := rfl
  have hf := fields_bound S
    (natBits (parentCap S A n m (count l) s c d P (rationalWordWidth source.prepared.budget)
      source.prepared.rangeBits source.exponent source.address)) (controls S A source) (by
        intro a ha
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        dsimp only [controls] at ha
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals unfold parentCap; omega)
  change fields S _ ≤ 15 * (natBits (parentCap S A n m (count l) s c d P
    (rationalWordWidth source.prepared.budget) source.prepared.rangeBits source.exponent source.address) + S) + 32 * S at hf
  dsimp only [window,profile]
  omega

end Blotto.GeneralPaperEqualSamplerCopyLifetime
