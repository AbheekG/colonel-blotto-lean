import Blotto.GeneralPaperStoredFreshWork
import Blotto.GeneralPaperStoredFreshDecoder

/-! The executed fresh decoder charges its countdown, single materialized
buffer and balanced decode. Its bound is uniform over the random-source
state and keeps the decoded bit length separate from address precision. -/
namespace Blotto.GeneralPaperStoredFreshDecoderWork
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def decodeBound (A count : ℕ) : ℕ :=
  (count + 1) + 6 * (count + 1) * binaryWordWidth (count + 1) +
    (2 * (count + 1) + 1) * (18 * binaryWordWidth (2 * (count + 1) + 4) + 8 + 16 * A)

def bound (model : RationalCostModel) (A count : ℕ) : ℕ :=
  GeneralPaperStoredFreshWork.bound model A count 0 + 64 * (count + 2) * A +
    decodeBound A count + 128 * (A + 1)

theorem work {S : Type*} (model : RationalCostModel) (A count : ℕ) (next : S → Bool × S) (state : S)
    (hA : 0 < A) (hCount : count + 2 < 2 ^ A) :
    (GeneralPaperStoredFreshDecoder.run model A count next state).work ≤ bound model A count := by
  let collected := GeneralPaperStoredFreshCollect.collect model A next count [] state
  have hLength : collected.bits.length = count + 1 := by
    simpa only [List.length_nil,Nat.add_zero] using GeneralPaperStoredFreshCollect.length model A next count [] state
  have hFresh := GeneralPaperStoredFreshWork.price_bound model A count 0 (by omega)
  have hBuffer := PaperListReferenceArray.bit_work A collected.bits hA
    (by rw [hLength]; exact binaryWordWidth_le_of_lt_pow hA hCount)
  rw [hLength] at hBuffer
  have hNext : count + 1 + 1 = count + 2 := by omega
  rw [hNext] at hBuffer
  have hDecode := GeneralPaperBalancedBitDecoder.work_bound (fun w => w) 1 (by intro w; omega)
    A collected.bits.toArray 0 (count + 1)
  have hMetadata : BinaryPayload.indexMetadataWordWidth collected.bits.toArray 0 (count + 1) =
      binaryWordWidth (2 * (count + 1) + 4) := by
    simp only [BinaryPayload.indexMetadataWordWidth,List.size_toArray,hLength,Nat.add_zero]
    congr 1
    omega
  rw [hMetadata] at hDecode
  rw [GeneralPaperStoredFreshDecoder.work]
  change _ ≤ bound model A count
  unfold bound decodeBound
  dsimp only [collected] at hBuffer hDecode
  norm_num only [Nat.mul_one,Nat.add_zero] at hDecode
  omega

theorem source_rank (model : RationalCostModel) (A count : ℕ) (fresh : Fin count → Bool) :
    (GeneralPaperStoredFreshDecoder.run model A count GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).value < 2 ^ count := by
  rw [(GeneralPaperStoredFreshDecoder.source model A count fresh).1]
  exact (balancedBitIndex count fresh).isLt

end Blotto.GeneralPaperStoredFreshDecoderWork
