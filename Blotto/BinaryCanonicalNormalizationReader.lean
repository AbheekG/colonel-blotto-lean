import Blotto.BinaryNormalizationPlan
import Blotto.BinaryCanonicalPayloadPlan
import Blotto.BinaryInputParserTraceSparsity
import Blotto.FareySourceUniverses

/-! A concrete canonical reader consumes planned normalization once. It retains
all preceding source/payload prices and forwards actual measured division work
plus reached normalization emission, including all rejection paths. Full-sampler
adoption and native/physical-space joins remain separate obligations. -/
namespace Blotto.BinaryCanonicalNormalizationReader
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryResourceTraceLength (under_length)
set_option autoImplicit false
set_option maxHeartbeats 4000000

def read (frame : List Bool) : (((Option ({word : SignedWord // CanonicalWord word} × List Bool) × Trace) × ℕ) × ℕ) × ℕ :=
  match frame with
  | [] => ((((none,wrap 8 1 []),4),0),0)
  | negative::rest =>
      let firstProduced := BinaryUnaryPayloadPlan.readWithEmission rest
      let first := firstProduced.1
      match first.1.1 with
      | none => ((((none,wrap 16 2 [first.1.2]),first.2+4),firstProduced.2),0)
      | some numerator =>
          let secondProduced := BinaryUnaryPayloadPlan.readWithEmission numerator.2
          let second := secondProduced.1
          match second.1.1 with
          | none => ((((none,wrap 24 2 [first.1.2,second.1.2]),first.2+second.2+8),firstProduced.2+secondProduced.2),0)
          | some denominator =>
              let tested := BooleanFreshSeedMeasured.scan denominator.1
              if hDen : tested.1.1 = true then
                let raw : SignedWord := ⟨negative,numerator.1,denominator.1⟩
                let produced := BinaryNormalizationPlan.canonicalize raw
                let normalized := produced.1.1
                have hValid : Valid raw := (BinaryEuclideanGCD.nonzero_true_iff _).mp
                  ((BinaryBooleanPrimitiveLifetime.scanWithTrace_erases denominator.1).symm.trans
                    ((congrArg Prod.fst (BooleanFreshSeedMeasured.scan_erases denominator.1)).symm.trans hDen))
                have hC : CanonicalWord normalized.1.1 := by
                  dsimp only [normalized,produced]
                  rw [BinaryNormalizationPlan.canonicalize_compat]
                  change CanonicalWord (BinaryQuadraticMeasured.canonicalize raw).1.1
                  rw [BinaryQuadraticMeasured.canonicalize_erases,
                    BinaryQuadraticLifetime.canonicalizeWithTrace_state raw hValid]
                  exact fromPayload_canonical negative numerator.1 denominator.1 hValid
                ((((some (⟨normalized.1.1,hC⟩,denominator.2),
                  wrap 64 2 [first.1.2,second.1.2,tested.1.2,normalized.1.2]),
                  first.2+second.2+tested.2+normalized.2+16),firstProduced.2+secondProduced.2),produced.1.2+produced.2)
              else ((((none,wrap 32 2 [first.1.2,second.1.2,tested.1.2]),
                first.2+second.2+tested.2+12),firstProduced.2+secondProduced.2),0)

theorem read_compat (frame : List Bool) : (read frame).1 = BinaryCanonicalPayloadPlan.read frame := by
  have hNorm (word : SignedWord) : (BinaryNormalizationPlan.canonicalize word).1.1 =
      BinaryQuadraticMeasured.canonicalize word := congrArg Prod.fst (BinaryNormalizationPlan.canonicalize_compat word)
  cases frame with
  | nil => rfl
  | cons negative rest =>
      simp only [read,BinaryCanonicalPayloadPlan.read,hNorm]
      cases hf : (BinaryUnaryPayloadPlan.readWithEmission rest).1.1.1 with
      | none => simp only [hf]
      | some numerator =>
          simp only [hf]
          cases hs : (BinaryUnaryPayloadPlan.readWithEmission numerator.2).1.1.1 with
          | none => simp only [hs]
          | some denominator =>
              simp only [hs]
              split <;> rename_i hDen <;> simp only [hDen]

theorem read_previous (frame : List Bool) : (read frame).1.1 = BinaryCanonicalFrameMeasured.read frame :=
  (congrArg Prod.fst (read_compat frame)).trans (BinaryCanonicalPayloadPlan.read_compat frame)

theorem read_price (frame : List Bool) :
    (read frame).2 ≤ 4*(read frame).1.1.2+25*(read frame).1.1.1.2.length+5 := by
  cases frame with
  | nil => simp [read]
  | cons negative rest =>
      unfold read
      dsimp only
      split
      · dsimp only; omega
      · rename_i numerator hn
        split
        · dsimp only; omega
        · rename_i denominator hd
          split
          · have he := BinaryNormalizationPlan.canonicalize_price (⟨negative,numerator.1,denominator.1⟩ : SignedWord)
            have hw := BinaryNormalizationPlan.canonicalize_division (⟨negative,numerator.1,denominator.1⟩ : SignedWord)
            dsimp only
            simp only [wrap,combine,List.length_append,List.length_cons,List.length_nil,under_length]
            omega
          · dsimp only; omega

theorem read_frame_bound (frame : List Bool) : (read frame).2 ≤ 300000*(frame.length+2)^3 := by
  have hp := read_price frame
  have hw := BinaryCanonicalFrameMeasured.read_work frame
  have hu := BinaryCanonicalFrameMeasured.read_usage frame
  have hs := BinaryMeasuredTraceSparsity.length_usage _ (BinaryInputParserTraceSparsity.canonical_bound frame)
  rw [← BinaryCanonicalFrameMeasured.read_erases] at hs
  rw [← read_previous] at hw hu hs
  let X := frame.length+2
  have hX : 0 < X := by dsimp [X]; omega
  have hOne : 1 ≤ X^3 := Nat.one_le_pow 3 X (by omega)
  have hLinear : X ≤ X^3 := by simpa only [pow_one] using Nat.pow_le_pow_right hX (by decide : 1 ≤ 3)
  have hSquare : (frame.length+1)^2 ≤ X^3 :=
    (Nat.pow_le_pow_left (by dsimp [X]; omega) 2).trans (Nat.pow_le_pow_right hX (by decide : 2 ≤ 3))
  have hWork := hw.trans (Nat.mul_le_mul_left 3000 hSquare)
  unfold BinaryCanonicalFrameMeasured.price at hw
  unfold BinaryCanonicalFrameLifetime.envelope at hu
  change _ ≤ 300000*X^3
  change usage (read frame).1.1.1.2 ≤ 3000*X^3+400*X at hu
  omega

theorem read_uniform : ∃ C d : ℕ,∀ frame : List Bool,(read frame).2 ≤ C*(frame.length+1)^d := by
  refine ⟨2400000,3,?_⟩
  intro frame
  calc
    (read frame).2 ≤ 300000*(frame.length+2)^3 := read_frame_bound frame
    _ ≤ 300000*(2*(frame.length+1))^3 :=
      Nat.mul_le_mul_left 300000 (Nat.pow_le_pow_left (by omega) 3)
    _ = 2400000*(frame.length+1)^3 := by ring

theorem read_joint (frame : List Bool) :
    (read frame).1.1.2+(read frame).1.2+(read frame).2+usage (read frame).1.1.1.2 ≤
      500000*(frame.length+2)^3 := by
  have hp := read_frame_bound frame
  have hw := BinaryCanonicalFrameMeasured.read_work frame
  have hu := BinaryCanonicalFrameMeasured.read_usage frame
  have hPayload := BinaryCanonicalPayloadPlan.read_price frame
  rw [← read_compat] at hPayload
  rw [← read_previous] at hw hu
  let X := frame.length+2
  have hX : 0 < X := by dsimp [X]; omega
  have hLinear : X ≤ X^3 := by simpa only [pow_one] using Nat.pow_le_pow_right hX (by decide : 1 ≤ 3)
  have hSquare : (frame.length+1)^2 ≤ X^3 :=
    (Nat.pow_le_pow_left (by dsimp [X]; omega) 2).trans (Nat.pow_le_pow_right hX (by decide : 2 ≤ 3))
  unfold BinaryCanonicalFrameMeasured.price at hw
  have hWork := hw.trans (Nat.mul_le_mul_left 3000 hSquare)
  unfold BinaryCanonicalFrameLifetime.envelope at hu
  change usage (read frame).1.1.1.2 ≤ 3000*X^3+400*X at hu
  change _ ≤ 500000*X^3
  change (read frame).2 ≤ 300000*X^3 at hp
  omega

theorem read_scalar_width (frame : List Bool) :
    ∀ counter ∈ [(read frame).1.1.2,(read frame).1.2,(read frame).2],
      binaryWordWidth counter ≤ binaryWordWidth 500000+1+3*binaryWordWidth (frame.length+2) := by
  have hj := read_joint frame
  have hm := binaryWordWidth_mul 500000 ((frame.length+2)^3)
  have hp := Farey.binaryWordWidth_power (frame.length+2) 3
  intro counter hc
  have hCounter : counter ≤ 500000*(frame.length+2)^3 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with h | h | h <;> subst counter <;> omega
  have hw := binaryWordWidth_mono hCounter
  omega

end Blotto.BinaryCanonicalNormalizationReader
