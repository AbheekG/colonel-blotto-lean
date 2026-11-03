import Blotto.GeneralPaperCachedMidpointAssembly

/-! Complete bit-priced midpoint producer: fresh reference buffer, fused
balanced rank decoder, stored-count rational assembly and wrapper metadata.
All size/height bounds below are erased certificates, not runtime oracles. -/
namespace Blotto.GeneralPaperEqualBitMidpoint
open GeneralPaperEqualPreparedCache (Prepared)
set_option autoImplicit false
set_option maxHeartbeats 900000

def indexWord (K : ℕ) : ℕ := binaryWordWidth (2 * K + 4) + 1

def run {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ) (fresh : Fin p.midpointBits → Bool) : (ℚ × ℕ) × ℕ :=
  let buffer := GeneralPaperNativeFreshBuffer.run (fun w => w) A fresh
  let decoded := GeneralPaperBalancedBitDecoder.run (fun w => w) A buffer.1.1.data 0 p.midpointBits
  let assembled := GeneralPaperCachedMidpointAssembly.run p model A decoded.value
  ((assembled.1, buffer.1.2), buffer.2 + decoded.work + assembled.2 + 32 * A + 32)

theorem data {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ) (fresh : Fin p.midpointBits → Bool) :
    (run p model A fresh).1.1 = GeneralPaperEqualPreparedCache.midpoint p fresh := by
  unfold run
  dsimp only
  rw [GeneralPaperNativeFreshBuffer.run_data, GeneralPaperBalancedBitDecoder.data]
  exact GeneralPaperCachedMidpointAssembly.data p model A fresh

theorem reads {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ) (fresh : Fin p.midpointBits → Bool) :
    (run p model A fresh).1.2 = p.midpointBits := GeneralPaperNativeFreshBuffer.run_reads _ _ _

theorem work {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ) (fresh : Fin p.midpointBits → Bool) :
    (run p model A fresh).2 ≤ 24 * model.rat (1 + 2 * GeneralPaperCachedMidpointAssembly.height p.midpointBits) +
      256 * (p.midpointBits + 1) * (A + indexWord p.midpointBits + 1) := by
  let K := p.midpointBits
  let buffer := GeneralPaperNativeFreshBuffer.run (fun w => w) A fresh
  let decoded := GeneralPaperBalancedBitDecoder.run (fun w => w) A buffer.1.1.data 0 K
  have hb := GeneralPaperNativeFreshBufferBits.work (fun w => w) monotone_id A fresh
  have hd := GeneralPaperBalancedBitDecoder.work_bound (fun w => w) 1 (fun _ => by omega) A buffer.1.1.data 0 K
  have hr : decoded.value < 2 ^ K := by
    rw [GeneralPaperBalancedBitDecoder.data]
    exact BinaryPayload.balancedValue_bounds _ _ _
  have ha := GeneralPaperCachedMidpointAssembly.work p model A decoded.value hr
  have hSize : buffer.1.1.data.size = K := buffer.1.1.size
  have hMeta : BinaryPayload.indexMetadataWordWidth buffer.1.1.data 0 K = binaryWordWidth (2 * K + 4) := by
    simp only [BinaryPayload.indexMetadataWordWidth, hSize, Nat.add_zero]
    congr 1
    omega
  rw [hMeta] at hd
  have h1 : binaryWordWidth (K + 2) ≤ indexWord K :=
    (binaryWordWidth_mono (by omega : K + 2 ≤ 2 * K + 4)).trans (Nat.le_succ _)
  have h2 : binaryWordWidth K ≤ indexWord K :=
    (binaryWordWidth_mono (by omega : K ≤ 2 * K + 4)).trans (Nat.le_succ _)
  have h3 : binaryWordWidth (2 * K + 4) ≤ indexWord K := Nat.le_succ _
  have hm1 := Nat.mul_le_mul_left (5 * K) h1
  have hm2 := Nat.mul_le_mul_left (6 * K) h2
  have hm3 := Nat.mul_le_mul_left ((2 * K + 1) * 18) h3
  change buffer.2 ≤ K * (5 * (1 + binaryWordWidth (K + 2)) + 64 * A + 1) + 64 * A at hb
  change decoded.work ≤ K + 6 * K * binaryWordWidth K +
    (2 * K + 1) * (18 * binaryWordWidth (2 * K + 4) + 8 + 16 * A) at hd
  change buffer.2 + decoded.work + (GeneralPaperCachedMidpointAssembly.run p model A decoded.value).2 + 32 * A + 32 ≤ _
  nlinarith only [hb, hd, ha, hm1, hm2, hm3]

end Blotto.GeneralPaperEqualBitMidpoint
