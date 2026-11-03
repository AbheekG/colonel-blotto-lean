import Blotto.GeneralPaperAlgorithmContract

/-! A proof-only uniform list view of the actual refined sampler. Entry
evaluation calls the retained-description sampler on the inverse binary
index; no list construction or enumeration is added to either program. -/
namespace Blotto.GeneralPaperUniformListSampler
open MeasureTheory
open GeneralPaperStoredStrategySampler (Sampler)
namespace Exact
export GeneralPaperExactStoredSampler (bits run law shifts shiftBits)
end Exact
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def length {n T K : ℕ} (sampler : Sampler n T K) : ℕ := 2 ^ Exact.bits sampler

noncomputable def entry {n T K : ℕ} (bitModel : Bool) (primitive : ℕ → ℕ) (A : ℕ)
    (model : RationalCostModel) (sampler : Sampler n T K) (poor : Bool)
    (i : Fin (length sampler)) : FixedArrayTable n ℚ :=
  (Exact.run bitModel primitive A model sampler poor ((bitIndexEquiv (Exact.bits sampler)).symm i)).output

theorem length_positive {n T K : ℕ} (sampler : Sampler n T K) : 0 < length sampler :=
  Nat.two_pow_pos _

theorem length_product {n T K : ℕ} (sampler : Sampler n T K) :
    length sampler = sampler.controls.rows * Exact.shifts sampler := by
  rw [length, GeneralPaperExactStoredSampler.bits, pow_add,
    ← sampler.controls.rows_power, ← GeneralPaperExactStoredSampler.shifts_power]

theorem actual_entry {n T K : ℕ} (bitModel : Bool) (primitive : ℕ → ℕ) (A : ℕ)
    (model : RationalCostModel) (sampler : Sampler n T K) (poor : Bool)
    (fresh : Fin (Exact.bits sampler) → Bool) :
    (Exact.run bitModel primitive A model sampler poor fresh).output =
      entry bitModel primitive A model sampler poor (bitIndex (Exact.bits sampler) fresh) := by
  simp only [entry]
  change _ = (Exact.run bitModel primitive A model sampler poor
    ((bitIndexEquiv (Exact.bits sampler)).symm ((bitIndexEquiv (Exact.bits sampler)) fresh))).output
  rw [Equiv.symm_apply_apply]

theorem uniform_law {n T K : ℕ} (bitModel : Bool) (primitive : ℕ → ℕ) (A : ℕ)
    (model : RationalCostModel) (sampler : Sampler n T K) (poor : Bool) :
    Exact.law bitModel primitive A model sampler poor =
      GeneralPaperUniformRowLaw.law (length_positive sampler)
        (fun i j => ((entry bitModel primitive A model sampler poor i).read j : ℝ)) := by
  have he : (fun fresh j => ((Exact.run bitModel primitive A model sampler poor fresh).output.read j : ℝ)) =
      (fun fresh j => ((entry bitModel primitive A model sampler poor
        (bitIndex (Exact.bits sampler) fresh)).read j : ℝ)) := by
    funext fresh j
    rw [actual_entry]
  change (fairBitLaw (Exact.bits sampler)).map _ = _
  rw [he]
  exact GeneralPaperFairIndexLaw.uniform (Exact.bits sampler)
    (fun i j => ((entry bitModel primitive A model sampler poor i).read j : ℝ))

theorem exact_random_bits {n T K : ℕ} (bitModel : Bool) (primitive : ℕ → ℕ) (A : ℕ)
    (model : RationalCostModel) (sampler : Sampler n T K) (poor : Bool)
    (fresh : Fin (Exact.bits sampler) → Bool) :
    (Exact.run bitModel primitive A model sampler poor fresh).freshReads = Nat.log2 (length sampler) := by
  rw [GeneralPaperExactStoredSampler.fresh_reads, length, Nat.log2_two_pow]

theorem every_entry_feasible {n T K : ℕ} (bitModel : Bool) (primitive : ℕ → ℕ) (A : ℕ)
    (model : RationalCostModel) (sampler : Sampler n T K) (poor : Bool) (B : ℝ)
    (h : Supported B (GeneralPaperStoredStrategySampler.law bitModel primitive A model sampler poor))
    (i : Fin (length sampler)) :
    Feasible B (fun j => ((entry bitModel primitive A model sampler poor i).read j : ℝ)) :=
  GeneralPaperExactStoredSampler.every_output_feasible bitModel primitive A model sampler poor B h _

theorem shift_bits_le {n T K : ℕ} (sampler : Sampler n T K) :
    Exact.shiftBits sampler ≤ sampler.controls.shiftBits := by
  rcases sampler with ⟨o, b, controls, description⟩
  cases description with
  | circle _ _ _ => exact le_rfl
  | direct _ _ => exact Nat.zero_le _

theorem random_bits_bound {n T K m k : ℕ} (sampler : Sampler n T K) (hm : m ≤ n)
    (hRows : sampler.controls.rowBits =
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rowBits)
    (hShifts : sampler.controls.shifts = GeneralPaperNativeSelectedSecurity.count k) :
    Nat.log2 (length sampler) ≤ 4*k + 2*binaryWordWidth (n+4) + 87 := by
  have hL : sampler.controls.shiftBits = k+6 := by
    have h := congrArg Nat.log2 (sampler.controls.shifts_power.symm.trans
      (hShifts.trans (GeneralPaperNativeSelectedSecurity.count_power k)))
    simpa only [Nat.log2_two_pow] using h
  have hr := GeneralPaperCachedArithmeticSampling.row_bits m n k hm
  have hs := shift_bits_le sampler
  rw [length, Nat.log2_two_pow]
  unfold GeneralPaperExactStoredSampler.bits
  rw [hL] at hs
  rw [hRows]
  omega

end Blotto.GeneralPaperUniformListSampler
