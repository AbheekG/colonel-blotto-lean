import Blotto.GeneralPaperEqualPreparedCopy

/-! Full retained bit sampler copy: all prepared rational/integer tables,
Boolean words/lists, precision and reference controls are materialized at
one destination width. Proof transport erases and does not recompute data. -/
namespace Blotto.GeneralPaperEqualSamplerCopy
open GeneralPaperEncodedScalarStorage GeneralPaperEqualRetainedStorage
open GeneralPaperPositiveSegmentCompaction (compact count)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem cache_transport_foot {n m r : ℕ} {G : RationalProportionalGroups n m}
    {l : RationalSegmentLottery m r} (A : ℕ) (p q : GeneralPaperEqualPreparedCache.Prepared G l)
    (h : p = q) (c : GeneralPaperEqualBooleanCache.Cache p) : cacheFoot A (h ▸ c) = cacheFoot A c := by
  cases h
  rfl

def run {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) :=
  let prepared := GeneralPaperEqualPreparedCopy.run S A source.prepared
  let hPrepared := GeneralPaperEqualPreparedCopy.data S A source.prepared
  let boolean := GeneralPaperEqualBooleanCopy.run S A source.categorical
  let categorical : GeneralPaperEqualBooleanCache.Cache prepared.1 := hPrepared.symm ▸ boolean.1
  let exponent := GeneralPaperReferenceCopy.scalar S A natBits source.exponent
  let address := GeneralPaperReferenceCopy.scalar S A natBits source.address
  let actual : GeneralPaperEqualStoredBitSampler.Sampler G l :=
    ⟨prepared.1,categorical,exponent.1,(by
      change prepared.1.midpointBits = source.exponent + 5
      rw [hPrepared]
      exact source.exponent_correct),address.1,(by
      change source.address = GeneralPaperEqualBitDrawRates.address n m source.exponent (rationalWordWidth prepared.1.budget)
      rw [hPrepared]
      exact source.address_correct)⟩
  (actual,prepared.2 + boolean.2 + exponent.2 + address.2 + 128 * (S + A + 1))

theorem data {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) : (run S A source).1 = source := by
  have hNew := GeneralPaperEqualBitCanonical.sampler_canonical (run S A source).1 source.exponent source.prepared.budget rfl rfl
  have hOld := GeneralPaperEqualBitCanonical.sampler_canonical source source.exponent source.prepared.budget rfl rfl
  exact hNew.trans hOld.symm

def price (S A n m r s c d P b w e a : ℕ) : ℕ :=
  GeneralPaperEqualPreparedCopy.price S A n m r s c d P b + GeneralPaperEqualBooleanCopy.price S A r w +
    natBits e + natBits a + 192 * (S + A + 1)

theorem work {n m r s c d P : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hl : (compact l).HeightAt s) (hc : ∀ j,RationalHeight (source.prepared.routes.table.read j).2 c)
    (hd : ∀ i,binaryWordWidth (source.prepared.counts.read i) ≤ d)
    (hp : ∀ x ∈ [source.prepared.D,source.prepared.rangeBits,source.prepared.midpointBits,source.prepared.midpointCount],natBits x ≤ P) :
    (run S A source).2 ≤ price S A n m (count l) s c d P (rationalWordWidth source.prepared.budget)
      source.prepared.rangeBits source.exponent source.address := by
  have hP := GeneralPaperEqualPreparedCopy.work S A source.prepared hl hc hd hp
  have hB := GeneralPaperEqualBooleanCopy.work S A source.categorical
  dsimp only [run,price,GeneralPaperReferenceCopy.scalar]
  omega

theorem charged {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) :
    footprint A (run S A source).1 ≤ 64 * (run S A source).2 := by
  have hP := GeneralPaperEqualPreparedCopy.charged S A source.prepared
  have hB := GeneralPaperEqualBooleanCopy.charged S A source.categorical
  dsimp only [run,footprint,GeneralPaperReferenceCopy.scalar]
  rw [cache_transport_foot]
  unfold fields
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  nlinarith

end Blotto.GeneralPaperEqualSamplerCopy
