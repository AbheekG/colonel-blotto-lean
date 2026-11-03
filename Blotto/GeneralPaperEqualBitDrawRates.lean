import Blotto.GeneralPaperEqualBitPostprocessing

/-! Local draw words/references and sharp bit-price majorants, derived from
native short cached fields. Original budget height enters additively; accuracy
encoding length is absent. No supplied runtime width/capacity oracle is used. -/
namespace Blotto.GeneralPaperEqualBitDrawRates
open GeneralPaperEqualNativeSampler (segmentHeight)
set_option autoImplicit false
set_option maxHeartbeats 900000

def size (n k b : ℕ) : ℕ := b + binaryWordWidth n + k + 10
def word (n k b : ℕ) : ℕ := 67108864 * size n k b
def log (n k b : ℕ) : ℕ := binaryWordWidth (n + word n k b + 32) + 1
def address (n m k b : ℕ) : ℕ := StoredArrayReferenceList.poolAddressWidth (n + m + k + 69) (word n k b)

theorem size_positive (n k b : ℕ) : 1 ≤ size n k b := by unfold size; omega

theorem word_bound (n k b : ℕ) :
    GeneralPaperEqualBitPostprocessing.word (segmentHeight n k) b (binaryWordWidth n + k + 9) (k + 5) ≤ word n k b := by
  have hs := GeneralPaperEqualNativeCache.segment_height_bound n k
  unfold GeneralPaperEqualBitPostprocessing.word GeneralPaperEqualBitPostprocessing.height
    GeneralPaperEqualBitPostprocessing.base expressionHeightBudget word size
  omega

theorem metadata_bounds (n m k b : ℕ) (hm : m ≤ 3) :
    address n m k b ≤ 2 * log n k b ∧
    GeneralPaperEqualBitPostprocessing.index n m (k + 5) ≤ 2 * log n k b ∧
    n + m + (k + 5) + 3 ≤ (n + 1) * size n k b := by
  have hw : m + k + 38 ≤ word n k b := by unfold word size; omega
  have h1 : binaryWordWidth ((n + m + k + 69) + 1) ≤ binaryWordWidth (n + word n k b + 32) :=
    binaryWordWidth_mono (by omega)
  have h2 : binaryWordWidth (word n k b + 1) ≤ binaryWordWidth (n + word n k b + 32) :=
    binaryWordWidth_mono (by omega)
  have hA := StoredArrayReferenceList.poolAddressWidth_log_bound (n + m + k + 69) (word n k b)
  have h3 : binaryWordWidth (2 * (k + 5) + 4) ≤ binaryWordWidth (n + word n k b + 32) := by
    apply binaryWordWidth_mono
    unfold word size
    omega
  have h4 : binaryWordWidth (n + m + 2) ≤ binaryWordWidth (n + word n k b + 32) := binaryWordWidth_mono (by omega)
  have hSize := Nat.mul_le_mul_left n (size_positive n k b)
  refine ⟨by unfold address log; omega, ?_, ?_⟩
  · unfold GeneralPaperEqualBitPostprocessing.index GeneralPaperEqualBitMidpoint.indexWord log
    omega
  · have hn := binaryWordWidth_pos n
    unfold size at hSize ⊢
    nlinarith only [hSize, hn, hm]

theorem post_bound (model : RationalCostModel) (n m k b : ℕ) (hm : m ≤ 3) :
    GeneralPaperEqualBitPostprocessing.bound model (address n m k b) n m (k + 5)
      (segmentHeight n k) b (binaryWordWidth n + k + 9) + 16 * address n m k b + 16 ≤
      16384 * (n + 1) * model.rat (word n k b) * log n k b := by
  let R := model.rat (word n k b)
  let L := log n k b
  have hL : 1 ≤ L := by dsimp [L, log]; omega
  have hW := model.monotone (word_bound n k b)
  have hMeta := metadata_bounds n m k b hm
  have hF : address n m k b + GeneralPaperEqualBitPostprocessing.index n m (k + 5) + 1 ≤ 5 * L := by
    change _ ≤ 5 * log n k b
    omega
  have hM := Nat.mul_le_mul hMeta.2.2 hF
  have hPrice : size n k b ≤ word n k b := by unfold word; omega
  have hR : size n k b ≤ R := hPrice.trans (model.word_le _)
  have hRW := Nat.mul_le_mul_left ((n + 1) * L) hR
  have hC : 24 + 25 * m + 5 * n ≤ 100 * (n + 1) := by omega
  have hP := Nat.mul_le_mul hC hW
  have hPL := Nat.mul_le_mul_left (100 * (n + 1) * R) hL
  have hExtra := Nat.mul_le_mul (show 1 ≤ n + 1 by omega) hR
  have hExtraL := Nat.mul_le_mul_left ((n + 1) * R) hL
  have hBase : 1 ≤ (n + 1) * R := (size_positive n k b).trans (by simpa only [Nat.one_mul] using hExtra)
  have hLB := Nat.mul_le_mul_right L hBase
  unfold GeneralPaperEqualBitPostprocessing.bound
  change _ ≤ 16384 * (n + 1) * R * L
  nlinarith only [hM, hRW, hP, hPL, hMeta.1, hExtra, hExtraL, hL, hLB]

end Blotto.GeneralPaperEqualBitDrawRates
