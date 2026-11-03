import Blotto.GeneralPaperOriginalBitHeadlines

/-! The direct identity-reduction route has S_out=1: consume only the row
block. It uses the retained dictionary columns and original budget. The
older padded-row interface remains available as checked reference evidence;
its unused shift block is absent from this actual output routine. -/
namespace Blotto.GeneralPaperDirectRowExactSampler
open MeasureTheory
open GeneralPaperSamplingOperandEnvelope (word_add)
set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxRecDepth 16384

def run {n m K : ℕ} (price index primitive : ℕ → ℕ) (A R T : ℕ) (hT : T = 2 ^ R)
    (hm : m = n) (c : ℚ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (fresh : Fin R → Bool) : GeneralPaperNativeFairSampler.Result n :=
  GeneralPaperDirectRowSampler.run price index primitive A R 0 T 1 hT (by simp) hm c columns fresh

noncomputable def law {n m K : ℕ} (price index primitive : ℕ → ℕ) (A R T : ℕ) (hT : T = 2 ^ R)
    (hm : m = n) (c : ℚ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) : Mixed n :=
  (fairBitLaw R).map (fun fresh j => ((run price index primitive A R T hT hm c columns fresh).output.read j : ℝ))

theorem fresh_reads {n m K : ℕ} (price index primitive : ℕ → ℕ) (A R T : ℕ) (hT : T = 2 ^ R)
    (hm : m = n) (c : ℚ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (fresh : Fin R → Bool) : (run price index primitive A R T hT hm c columns fresh).freshReads = R :=
  GeneralPaperDirectRowSampler.fresh_reads price index primitive A R 0 T 1 hT (by simp) hm c columns fresh

theorem logarithmic_bits {n m K : ℕ} (price index primitive : ℕ → ℕ) (A R T : ℕ) (hT : T = 2 ^ R)
    (hm : m = n) (c : ℚ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (fresh : Fin R → Bool) : (run price index primitive A R T hT hm c columns fresh).freshReads = Nat.log2 (T * 1) := by
  rw [fresh_reads, hT, Nat.mul_one, Nat.log2_two_pow]

theorem first_block (R : ℕ) (fresh : Fin R → Bool) : firstBitBlock R 0 fresh = fresh := by
  funext j
  apply congrArg fresh
  apply Fin.ext
  rfl

theorem data {n m K : ℕ} (price index primitive : ℕ → ℕ) (A R T : ℕ) (hT : T = 2 ^ R)
    (hm : m = n) (c : ℚ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (fresh : Fin R → Bool) : (run price index primitive A R T hT hm c columns fresh).output =
      (GeneralPaperDirectRowSampler.draw price index A hm c columns (Fin.cast hT.symm (bitIndex R fresh))).1 := by
  unfold run
  rw [GeneralPaperDirectRowSampler.data, first_block]

theorem old_output {n m K : ℕ} (price index primitive : ℕ → ℕ) (A R L T S : ℕ)
    (hT : T = 2 ^ R) (hS : S = 2 ^ L) (hm : m = n) (c : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (fresh : Fin (R + L) → Bool) :
    (GeneralPaperDirectRowSampler.run price index primitive A R L T S hT hS hm c columns fresh).output =
      (run price index primitive A R T hT hm c columns (firstBitBlock R L fresh)).output := by
  rw [GeneralPaperDirectRowSampler.data, data]

theorem old_law {n m K : ℕ} (price index primitive : ℕ → ℕ) (A R L T S : ℕ)
    (hT : T = 2 ^ R) (hS : S = 2 ^ L) (hm : m = n) (c : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    law price index primitive A R T hT hm c columns =
      GeneralPaperDirectRowSampler.law price index primitive A R L T S hT hS hm c columns := by
  change GeneralPaperDirectRowSampler.law price index primitive A R 0 T 1 hT (by simp) hm c columns = _
  rw [GeneralPaperDirectRowSampler.law_data, GeneralPaperDirectRowSampler.law_data]

theorem arithmetic_work {n m K : ℕ} (R T : ℕ) (hT : T = 2 ^ R) (hm : m = n) (c : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (fresh : Fin R → Bool) :
    (run (fun _ => 1) (fun _ => 1) (fun _ => 1) 1 R T hT hm c columns fresh).work ≤ 282 * n + 144 * R + 410 :=
  GeneralPaperDirectRowSampler.run_arithmetic_work R 0 T 1 hT (by simp) hm c columns fresh

theorem bit_work {n m K : ℕ} (model : RationalCostModel) (A C H R T : ℕ) (hA : 1 ≤ A)
    (hT : T = 2 ^ R) (hm : m = n) (c : ℚ) (hc : RationalHeight c C)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (hColumns : ∀ j l, RationalHeight ((columns.read j).anchors.read l) H)
    (hIndex : ∀ i ≤ n, binaryWordWidth (i + 1) ≤ A) (fresh : Fin R → Bool) :
    (run model.rat id model.rat A R T hT hm c columns fresh).work ≤
      GeneralPaperCachedBitSampling.directProfile model A R 0 C H n :=
  GeneralPaperCachedBitSampling.direct_work model A C H R 0 T 1 hA hT (by simp) hm c hc columns hColumns hIndex fresh

theorem profile_mono (model : RationalCostModel) (A R L C H n : ℕ) :
    GeneralPaperCachedBitSampling.directProfile model A R 0 C H n ≤
      GeneralPaperCachedBitSampling.directProfile model A R L C H n := by
  have hF := model.monotone (Nat.add_le_add_left (binaryWordWidth_mono
    (show R + 2 ≤ R + L + 2 by omega)) 1)
  have hI := model.monotone (Nat.add_le_add_left (binaryWordWidth_mono
    (show R + 2 ^ R + 2 ≤ R + L + 2 ^ R + 2 by omega)) 1)
  have hFM : R * (5 * model.rat (1 + binaryWordWidth (R + 2)) + 64 * A + 1) ≤
      (R + L) * (5 * model.rat (1 + binaryWordWidth (R + L + 2)) + 64 * A + 1) := by
    apply Nat.mul_le_mul (by omega)
    omega
  have hIM := Nat.mul_le_mul_left R (show
      10 * model.rat (1 + binaryWordWidth (R + 2 ^ R + 2)) + 64 * A ≤
      10 * model.rat (1 + binaryWordWidth (R + L + 2 ^ R + 2)) + 64 * A by omega)
  unfold GeneralPaperCachedBitSampling.directProfile GeneralPaperNativeFreshBufferBits.profile
    GeneralPaperNativeFreshBufferBits.width GeneralPaperNativeDyadicBlocksBits.profile
    GeneralPaperNativeFairIndexBits.width GeneralPaperNativeFairIndexBits.magnitude
  simp only [Nat.add_zero, Nat.zero_mul]
  omega

theorem independent_players {n m K : ℕ} (price index primitive : ℕ → ℕ) (A R T : ℕ)
    (hT : T = 2 ^ R) (hm : m = n) (c d : ℚ)
    (rich poor : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    Measure.map (fun fresh =>
      ((fun j => ((run price index primitive A R T hT hm c rich (firstBitBlock R R fresh)).output.read j : ℝ)),
       (fun j => ((run price index primitive A R T hT hm d poor (secondBitBlock R R fresh)).output.read j : ℝ))))
      (fairBitLaw (R + R) : Measure (Fin (R + R) → Bool)) =
      (law price index primitive A R T hT hm c rich : Measure (Allocation n)).prod
        (law price index primitive A R T hT hm d poor : Measure (Allocation n)) :=
  fairBitBlocks_map_product R R
    (fun fresh j => ((run price index primitive A R T hT hm c rich fresh).output.read j : ℝ))
    (fun fresh j => ((run price index primitive A R T hT hm d poor fresh).output.read j : ℝ))

end Blotto.GeneralPaperDirectRowExactSampler
