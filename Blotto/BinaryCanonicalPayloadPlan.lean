import Blotto.BinaryUnaryPayloadPlan
import Blotto.BinaryCanonicalFrameMeasured

/-! Canonical signed-word parsing consumes the actual planned payload reader.
Its complete old canonical/data/trace/source record is exact, with reached
payload emissions returned separately. Other arithmetic/scan scopes remain. -/
namespace Blotto.BinaryCanonicalPayloadPlan
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 3000000

def read (frame : List Bool) : ((Option ({word : SignedWord // CanonicalWord word} × List Bool) × Trace) × ℕ) × ℕ :=
  match frame with
  | [] => (((none,wrap 8 1 []),4),0)
  | negative::rest =>
      let firstProduced := BinaryUnaryPayloadPlan.readWithEmission rest
      let first := firstProduced.1
      match first.1.1 with
      | none => (((none,wrap 16 2 [first.1.2]),first.2+4),firstProduced.2)
      | some numerator =>
          let secondProduced := BinaryUnaryPayloadPlan.readWithEmission numerator.2
          let second := secondProduced.1
          match second.1.1 with
          | none => (((none,wrap 24 2 [first.1.2,second.1.2]),first.2+second.2+8),firstProduced.2+secondProduced.2)
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
                (((some (⟨normalized.1.1,hC⟩,denominator.2),
                  wrap 64 2 [first.1.2,second.1.2,tested.1.2,normalized.1.2]),
                  first.2+second.2+tested.2+normalized.2+16),firstProduced.2+secondProduced.2)
              else (((none,wrap 32 2 [first.1.2,second.1.2,tested.1.2]),
                first.2+second.2+tested.2+12),firstProduced.2+secondProduced.2)

theorem read_compat (frame : List Bool) :
    (read frame).1 = BinaryCanonicalFrameMeasured.read frame := by
  cases frame with
  | nil => rfl
  | cons negative rest =>
      simp only [read,BinaryCanonicalFrameMeasured.read,BinaryUnaryPayloadPlan.read_compat]
      cases hf : (BinaryUnaryPayloadMeasured.read rest).1.1 with
      | none => simp only [hf]
      | some numerator =>
          simp only [hf]
          cases hs : (BinaryUnaryPayloadMeasured.read numerator.2).1.1 with
          | none => simp only [hs]
          | some denominator =>
              simp only [hs]
              split <;> rename_i hDen <;> simp only [hDen]

theorem read_price (frame : List Bool) : (read frame).2 ≤ 30*(read frame).1.2 := by
  cases frame with
  | nil => change 0 ≤ 30*4; omega
  | cons negative rest =>
      have hf := BinaryUnaryPayloadPlan.read_price rest
      unfold read
      dsimp only
      split
      · dsimp only; omega
      · rename_i numerator hn
        have hs := BinaryUnaryPayloadPlan.read_price numerator.2
        split
        · dsimp only; omega
        · split <;> dsimp only <;> omega

theorem read_suffix_lt (frame : List Bool) (parsed : {word : SignedWord // CanonicalWord word} × List Bool)
    (h : (read frame).1.1.1 = some parsed) : parsed.2.length < frame.length :=
  BinaryCanonicalFrameMeasured.read_suffix_lt frame parsed ((congrArg (fun out => out.1.1) (read_compat frame)).symm.trans h)

end Blotto.BinaryCanonicalPayloadPlan
