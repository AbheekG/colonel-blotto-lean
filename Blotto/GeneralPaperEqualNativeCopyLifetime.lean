import Blotto.GeneralPaperEqualSamplerCopyLifetime

/-! Native instantiation of the complete grouped-copy lifetime. Every
retained field bound and every destination index-width premise is derived
from the actual rounded producer and stored local reference. -/
namespace Blotto.GeneralPaperEqualNativeCopyLifetime
open GeneralPaperEqualNativeRetainedStorage (height short)
open GeneralPaperEqualBitDrawRates (log address)
open GeneralPaperEqualNativeSampler (rounded segmentHeight)
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384

structure Cursor {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (source : GeneralPaperEqualStoredBitSampler.Sampler G l) where
  route : Fin (n + 1)
  slot : Fin (count l + 1)
  group : Fin (m + 1)
  row : Option {x : Fin (count l) × FixedBinaryWord (source.prepared.rangeBits + 1) // x ∈ source.categorical.rows}

def window {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) (cursor : Cursor source) : ℕ :=
  GeneralPaperEqualSamplerCopyLifetime.window S A source cursor.route.val (by omega)
    cursor.slot.val (by omega) cursor.group.val (by omega) cursor.row

def profile (S n k b : ℕ) : ℕ :=
  GeneralPaperEqualSamplerCopyLifetime.profile S (2 * log n k b) n 3 7
    (height n k) (height n k) (height n k) (height n k) b (height n k) k (2 * log n k b)

theorem profile_mono (S n b e : ℕ) {A B m M r R s T c C d D P Q w V a z : ℕ}
    (hA : A ≤ B) (hm : m ≤ M) (hr : r ≤ R) (hs : s ≤ T) (hc : c ≤ C) (hd : d ≤ D)
    (hP : P ≤ Q) (hw : w ≤ V) (ha : a ≤ z) :
    GeneralPaperEqualSamplerCopyLifetime.profile S A n m r s c d P b w e a ≤
      GeneralPaperEqualSamplerCopyLifetime.profile S B n M R T C D Q b V e z := by
  unfold GeneralPaperEqualSamplerCopyLifetime.profile GeneralPaperEqualSamplerCopyLifetime.ownerProfile
    GeneralPaperEqualSamplerCopyLifetime.parentCap GeneralPaperEqualPreparedCopyLifetime.profile
    GeneralPaperEqualPreparedCopyLifetime.parentCap GeneralPaperEqualRouteCopyLifetime.profile
    GeneralPaperEqualRouteCopyLifetime.parentCap GeneralPaperEqualRouteCopyLifetime.payload
    GeneralPaperEqualSegmentCopyLifetime.profile GeneralPaperEqualSegmentCopyLifetime.parentCap
    GeneralPaperEqualBooleanCopyLifetime.profile GeneralPaperEqualBooleanCopyLifetime.parentCap
    GeneralPaperEqualBooleanCopyLifetime.rowPayload GeneralPaperEqualBooleanRowCopyLifetime.profile
    GeneralPaperEqualBooleanRowCopyLifetime.parentCap GeneralPaperEqualBooleanRowCopyLifetime.price
    GeneralPaperEqualBooleanWordCopyLifetime.profile GeneralPaperEqualBooleanWordCopyLifetime.parentCap
    GeneralPaperEqualBooleanWordCopyLifetime.bitPrice GeneralPaperMatrixCopyLifetime.profile
    GeneralPaperScalarTableCopyLifetime.profile GeneralPaperScalarTableCopyLifetime.scalarProfile
    GeneralPaperScalarTableCopyLifetime.scalarPrice GeneralPaperReferenceArrayCopyLifetime.profile
    GeneralPaperReferenceArrayCopyLifetime.parentCap GeneralPaperDualWidthFillStorage.profile
    GeneralPaperAdditivePayloadFillStorage.profile GeneralPaperNativePayloadFillStorage.frameProfile
    GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperNativePayloadFillStorage.workCap
    GeneralPaperReferenceListCopyLifetime.profile GeneralPaperReferenceListCopyLifetime.frameProfile
    GeneralPaperReferenceListCopyLifetime.metadataCap GeneralPaperReferenceListCopyLifetime.workCap
    GeneralPaperEqualRetainedStorage.preparedProfile GeneralPaperEqualRetainedStorage.cacheProfile
    GeneralPaperEqualRetainedStorage.segmentProfile GeneralPaperEqualRetainedStorage.wordProfile
    GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperEqualSamplerCopy.price
    GeneralPaperEqualPreparedCopy.price GeneralPaperEqualRationalCopy.routesPrice
    GeneralPaperEqualRationalCopy.segmentsPrice GeneralPaperScalarTableCopy.matrixPrice
    GeneralPaperScalarTableCopy.price GeneralPaperReferenceCopy.arrayPrice
    GeneralPaperEqualBooleanCopy.price GeneralPaperEqualBooleanCopy.wordPrice GeneralPaperEncodedScalarStorage.natBits
  gcongr

theorem address_indices (n m k b r : ℕ) (hr : r ≤ 7) :
    1 ≤ address n m k b ∧ binaryWordWidth (n + 1) ≤ address n m k b ∧
      binaryWordWidth (m + 1) ≤ address n m k b ∧ binaryWordWidth (r + 1) ≤ address n m k b := by
  have hMul := Nat.mul_le_mul_left (n + m + k + 69)
    (show 1 ≤ GeneralPaperEqualBitDrawRates.word n k b + 1 by omega)
  unfold address StoredArrayReferenceList.poolAddressWidth
  refine ⟨by unfold binaryWordWidth; omega,?_,?_,?_⟩
  all_goals apply binaryWordWidth_mono; nlinarith only [hMul,hr]

theorem native {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let a := GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget
    ∀ cursor : Cursor a,window S a.address a cursor ≤ profile S n k (rationalWordWidth budget) := by
  dsimp only
  let a := GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget
  intro cursor
  have hm := GeneralPaperEqualNativeCache.group_count (rounded true model W k values v hv) small
  have hr := (GeneralPaperEqualNativeCache.compact_count (rounded true model W k values v hv) small).2
  have hIndices := address_indices n (terminal (rounded true model W k values v hv) small).groups.length
    k (rationalWordWidth budget) (count (lottery (rounded true model W k values v hv) small)) hr
  have h := GeneralPaperEqualSamplerCopyLifetime.all_cursors S a.address a
    (GeneralPaperPositiveSegmentCompaction.compact_height _
      (GeneralPaperEqualNativeSampler.native_lottery_height true model W k values v hv small))
    (GeneralPaperEqualNativeCache.route_height true model W k values v hv small budget)
    (GeneralPaperEqualNativeCache.count_word true model W k values v hv small budget)
    (GeneralPaperEqualNativeRetainedStorage.native_controls true model W k values v hv small budget)
    hIndices.1 hIndices.2.1 hIndices.2.2.1 hIndices.2.2.2
    cursor.route.val (by omega) cursor.slot.val (by omega) cursor.group.val (by omega) cursor.row
  have hA := (GeneralPaperEqualBitDrawRates.metadata_bounds n _ k (rationalWordWidth budget) hm).1
  change a.address ≤ 2 * log n k (rationalWordWidth budget) at hA
  have hs : segmentHeight n k ≤ height n k := by
    have hx := GeneralPaperEqualNativeCache.segment_height_bound n k
    dsimp only [height,short]
    omega
  have hc : binaryWordWidth n + k + 9 ≤ height n k := by dsimp only [height,short]; omega
  have hd : 3670016 * (binaryWordWidth n + k + 10) + 1 ≤ height n k := by dsimp only [height,short]; omega
  have hw := (GeneralPaperEqualNativeCache.rangeBits true model W k values v hv small budget).trans hd
  apply h.trans
  unfold profile
  exact profile_mono S n (rationalWordWidth budget) k hA hm hr hs hc hd le_rfl hw hA

end Blotto.GeneralPaperEqualNativeCopyLifetime
