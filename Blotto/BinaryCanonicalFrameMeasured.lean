import Blotto.BinaryUnaryPayloadMeasured
import Blotto.BinaryCanonicalFrameLifetime
import Blotto.BinaryQuadraticMeasured

/-! One signed rational reader executes the paired Boolean payload readers,
denominator scan and actual quadratic canonicalizer. The source charge uses
the quadratic backend actually called, including rejecting inputs; no old
Euclidean normalization price or retained-space bound is used as work. -/
namespace Blotto.BinaryCanonicalFrameMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 3000000

def read (frame : List Bool) : (Option ({word : SignedWord // CanonicalWord word} × List Bool) × Trace) × ℕ :=
  match frame with
  | [] => ((none,wrap 8 1 []),4)
  | negative::rest =>
      let first := BinaryUnaryPayloadMeasured.read rest
      match first.1.1 with
      | none => ((none,wrap 16 2 [first.1.2]),first.2+4)
      | some numerator =>
          let second := BinaryUnaryPayloadMeasured.read numerator.2
          match second.1.1 with
          | none => ((none,wrap 24 2 [first.1.2,second.1.2]),first.2+second.2+8)
          | some denominator =>
              let tested := BooleanFreshSeedMeasured.scan denominator.1
              if hDen : tested.1.1 = true then
                let raw : SignedWord := ⟨negative,numerator.1,denominator.1⟩
                let normalized := BinaryQuadraticMeasured.canonicalize raw
                have hValid : Valid raw := (BinaryEuclideanGCD.nonzero_true_iff _).mp
                  ((BinaryBooleanPrimitiveLifetime.scanWithTrace_erases denominator.1).symm.trans
                    ((congrArg Prod.fst (BooleanFreshSeedMeasured.scan_erases denominator.1)).symm.trans hDen))
                have hC : CanonicalWord normalized.1.1 := by
                  rw [BinaryQuadraticMeasured.canonicalize_erases,
                    BinaryQuadraticLifetime.canonicalizeWithTrace_state raw hValid]
                  exact fromPayload_canonical negative numerator.1 denominator.1 hValid
                ((some (⟨normalized.1.1,hC⟩,denominator.2),
                  wrap 64 2 [first.1.2,second.1.2,tested.1.2,normalized.1.2]),
                  first.2+second.2+tested.2+normalized.2+16)
              else ((none,wrap 32 2 [first.1.2,second.1.2,tested.1.2]),first.2+second.2+tested.2+12)

theorem read_erases (frame : List Bool) :
    (read frame).1 = BinaryCanonicalFrameLifetime.readWithTrace frame := by
  cases frame with
  | nil => rfl
  | cons negative rest =>
      unfold read BinaryCanonicalFrameLifetime.readWithTrace
      dsimp only
      simp only [BinaryUnaryPayloadMeasured.read_erases,BooleanFreshSeedMeasured.scan_erases,
        BinaryQuadraticMeasured.canonicalize_erases]
      cases (BinaryUnaryPayloadLifetime.readWithTrace rest).1 with
      | none => rfl
      | some numerator =>
          dsimp only
          cases (BinaryUnaryPayloadLifetime.readWithTrace numerator.2).1 with
          | none => rfl
          | some denominator =>
              dsimp only
              split <;> rfl

def price (length : ℕ) : ℕ := 3000*(length+1)^2

theorem price_mono {a b : ℕ} (h : a ≤ b) : price a ≤ price b := by unfold price; gcongr

theorem read_work (frame : List Bool) : (read frame).2 ≤ price frame.length := by
  cases frame with
  | nil => norm_num [read,price]
  | cons negative rest =>
      have hFirst := BinaryUnaryPayloadMeasured.read_work rest
      unfold read
      dsimp only
      split
      · unfold price
        simp only [List.length_cons]
        nlinarith
      · rename_i numerator hn
        have hN := BinaryUnaryPayloadMeasured.read_payload_length rest numerator hn
        have hTail := BinaryUnaryPayloadMeasured.read_suffix_lt rest numerator hn
        have hSecond := BinaryUnaryPayloadMeasured.read_work numerator.2
        split
        · unfold price
          simp only [List.length_cons]
          nlinarith
        · rename_i denominator hd
          have hD := BinaryUnaryPayloadMeasured.read_payload_length numerator.2 denominator hd
          have hScan := BooleanFreshSeedMeasured.scan_bound denominator.1
          split
          · have hNorm := BinaryQuadraticNormalization.canonicalizeWithWork_bound
              (⟨negative,numerator.1,denominator.1⟩ : SignedWord)
            rw [← BinaryQuadraticMeasured.canonicalize_work] at hNorm
            have hWidth : width (⟨negative,numerator.1,denominator.1⟩ : SignedWord)+1 ≤ 2*(rest.length+1) := by
              simp only [width]
              omega
            have hNorm' := hNorm.trans (Nat.mul_le_mul_left 600 (Nat.pow_le_pow_left hWidth 2))
            unfold price
            simp only [List.length_cons]
            nlinarith
          · unfold price
            simp only [List.length_cons]
            nlinarith

theorem read_suffix_lt (frame : List Bool) (parsed : {word : SignedWord // CanonicalWord word} × List Bool)
    (h : (read frame).1.1 = some parsed) : parsed.2.length < frame.length :=
  BinaryCanonicalFrameLifetime.read_suffix_lt frame parsed
    ((congrArg Prod.fst (read_erases frame)).symm.trans h)

theorem read_usage (frame : List Bool) :
    usage (read frame).1.2 ≤ BinaryCanonicalFrameLifetime.envelope frame.length := by
  rw [read_erases]
  exact BinaryCanonicalFrameLifetime.readWithTrace_usage frame

theorem all_prefix (frame : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+frame.length) (read frame).1.2 steps ≤
      borrowed+frame.length+BinaryCanonicalFrameLifetime.envelope frame.length ∧
    framePeak ((read frame).1.2.take steps) ≤ BinaryCanonicalFrameLifetime.envelope frame.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (read_usage frame) _ steps

end Blotto.BinaryCanonicalFrameMeasured
