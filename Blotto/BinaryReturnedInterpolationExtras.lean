import Blotto.BinaryNormalizationExtraWork

/-! Actual interpolation and packed-point records forward normalization extras
from one execution. Exact observer equalities transfer their existing bounds;
prefix bounds price this named component, not full native runtime/storage. -/
namespace Blotto.BinaryReturnedInterpolationExtras
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryWordObjectArray (Store)
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem loop_extra {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord)
    (indices : List (List Bool)) :
    (BinaryPhysicalInterpolationMeasured.loopWithExtras first second scalar indices).2 =
      BinaryNormalizationExtraWork.interpolationLoop first second scalar indices := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      simp only [BinaryPhysicalInterpolationMeasured.loopWithExtras,BinaryNormalizationExtraWork.interpolationLoop]
      cases hp : (BinaryWordObjectArrayAccessMeasured.get first index).1.1 with
      | none => simp only [hp]
      | some p =>
          simp only [hp]
          cases hq : (BinaryWordObjectArrayAccessMeasured.get second index).1.1 with
          | none => simp only [hq]
          | some q => simp only [hq,ih]

theorem run_extra (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length=q.length) :
    (BinaryPhysicalInterpolationMeasured.runWithExtras scalar p q hLength).2 =
      BinaryNormalizationExtraWork.interpolationRun scalar p q := by
  simp only [BinaryPhysicalInterpolationMeasured.runWithExtras,BinaryNormalizationExtraWork.interpolationRun,loop_extra]

theorem stage_extra (p q : List SignedWord) (seed : List Bool) (hLength : p.length=q.length) :
    (BinaryPhysicalPointMeasured.stageWithExtras p q seed hLength).2 =
      BinaryNormalizationExtraWork.pointStage p q seed := by
  simp only [BinaryPhysicalPointMeasured.stageWithExtras,BinaryNormalizationExtraWork.pointStage,run_extra]

theorem sample_extra {n k : ℕ} (table : BinaryStoredOverlapEnvironment.Segment n k) (slot : Fin k)
    (K : ℕ) (bits : BinaryScalarTape K) :
    (BinaryPhysicalPointMeasured.sampleWithExtras table slot K bits).2 =
      BinaryNormalizationExtraWork.point table slot K bits := by
  simp only [BinaryPhysicalPointMeasured.sampleWithExtras,BinaryNormalizationExtraWork.point,stage_extra]

theorem loop_bound {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord)
    (indices : List (List Bool)) :
    (BinaryPhysicalInterpolationMeasured.loopWithExtras first second scalar indices).2 ≤
      155*(BinaryPhysicalInterpolationMeasured.loopWithExtras first second scalar indices).1.2 := by
  simpa only [loop_extra,BinaryPhysicalInterpolationMeasured.loopWithExtras_compat] using
    BinaryNormalizationExtraWork.interpolationLoop_bound first second scalar indices

theorem run_bound (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length=q.length) :
    (BinaryPhysicalInterpolationMeasured.runWithExtras scalar p q hLength).2 ≤
      155*(BinaryPhysicalInterpolationMeasured.runWithExtras scalar p q hLength).1.2 := by
  simpa only [run_extra,BinaryPhysicalInterpolationMeasured.runWithExtras_compat] using
    BinaryNormalizationExtraWork.interpolationRun_bound scalar p q hLength

theorem run_price (scalar : SignedWord) (p q : List SignedWord) (hLength : p.length=q.length)
    (hT : BinaryRationalOpcode.Valid scalar) (W : ℕ) (hW : 1 ≤ W) (ht : width scalar ≤ W)
    (hp : ∀ word ∈ p,BinaryRationalOpcode.Valid word ∧ width word ≤ W)
    (hq : ∀ word ∈ q,BinaryRationalOpcode.Valid word ∧ width word ≤ W) :
    (BinaryPhysicalInterpolationMeasured.runWithExtras scalar p q hLength).1.2+
      (BinaryPhysicalInterpolationMeasured.runWithExtras scalar p q hLength).2 ≤
      156*BinaryPhysicalInterpolationRun.bound p.length W := by
  simpa only [run_extra,BinaryPhysicalInterpolationMeasured.runWithExtras_compat] using
    BinaryNormalizationExtraWork.interpolationRun_full scalar p q hLength hT W hW ht hp hq

theorem stage_bound (p q : List SignedWord) (seed : List Bool) (hLength : p.length=q.length) :
    (BinaryPhysicalPointMeasured.stageWithExtras p q seed hLength).2 ≤
      155*(BinaryPhysicalPointMeasured.stageWithExtras p q seed hLength).1.2 := by
  simpa only [stage_extra,BinaryPhysicalPointMeasured.stageWithExtras_compat] using
    BinaryNormalizationExtraWork.pointStage_bound p q seed hLength

theorem stage_price (p q : List SignedWord) (seed : List Bool) (hLength : p.length=q.length)
    (W : ℕ) (hCap : seed.length+2 ≤ W)
    (hp : ∀ word ∈ p,BinaryRationalOpcode.Valid word ∧ width word ≤ W)
    (hq : ∀ word ∈ q,BinaryRationalOpcode.Valid word ∧ width word ≤ W) :
    (BinaryPhysicalPointMeasured.stageWithExtras p q seed hLength).1.2+
      (BinaryPhysicalPointMeasured.stageWithExtras p q seed hLength).2 ≤
      156*BinaryTapePointLifetime.bound p.length W seed.length := by
  simpa only [stage_extra,BinaryPhysicalPointMeasured.stageWithExtras_compat] using
    BinaryNormalizationExtraWork.pointStage_price p q seed hLength W hCap hp hq

theorem sample_bound {n k : ℕ} (table : BinaryStoredOverlapEnvironment.Segment n k) (slot : Fin k)
    (K : ℕ) (bits : BinaryScalarTape K) :
    (BinaryPhysicalPointMeasured.sampleWithExtras table slot K bits).2 ≤
      155*(BinaryPhysicalPointMeasured.sampleWithExtras table slot K bits).1.2 := by
  simpa only [sample_extra,BinaryPhysicalPointMeasured.sampleWithExtras_compat] using
    BinaryNormalizationExtraWork.point_bound table slot K bits

theorem sample_price {n k : ℕ} (table : BinaryStoredOverlapEnvironment.Segment n k) (hC : table.Canonical)
    (s : ℕ) (hH : ∀ slot j,RationalHeight (value ((table.P.read slot).read j)) s ∧
      RationalHeight (value ((table.Q.read slot).read j)) s) (slot : Fin k) (K : ℕ) (bits : BinaryScalarTape K) :
    (BinaryPhysicalPointMeasured.sampleWithExtras table slot K bits).1.2+
      (BinaryPhysicalPointMeasured.sampleWithExtras table slot K bits).2 ≤
      156*BinaryPhysicalPointMeasured.price n s K := by
  simpa only [sample_extra,BinaryPhysicalPointMeasured.sampleWithExtras_compat] using
    BinaryNormalizationExtraWork.point_price table hC s hH slot K bits

theorem prefix_mono {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord)
    (indices : List (List Bool)) (steps : ℕ) :
    (BinaryPhysicalInterpolationMeasured.loopWithExtras first second scalar (indices.take steps)).2 ≤
      (BinaryPhysicalInterpolationMeasured.loopWithExtras first second scalar indices).2 := by
  induction indices generalizing steps with
  | nil => simp only [List.take_nil]; exact Nat.le_refl _
  | cons index indices ih =>
      cases steps with
      | zero => simp only [List.take_zero,BinaryPhysicalInterpolationMeasured.loopWithExtras]; exact Nat.zero_le _
      | succ steps =>
          simp only [List.take_succ_cons,BinaryPhysicalInterpolationMeasured.loopWithExtras]
          cases hp : (BinaryWordObjectArrayAccessMeasured.get first index).1.1 with
          | none => simp only [hp]; omega
          | some p =>
              simp only [hp]
              cases hq : (BinaryWordObjectArrayAccessMeasured.get second index).1.1 with
              | none => simp only [hq]; omega
              | some q =>
                  simp only [hq]
                  have h := ih steps
                  omega

theorem prefix_bound {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord)
    (indices : List (List Bool)) (steps : ℕ) :
    (BinaryPhysicalInterpolationMeasured.loopWithExtras first second scalar (indices.take steps)).2 ≤
      155*(BinaryPhysicalInterpolationMeasured.loopWithExtras first second scalar indices).1.2 := by
  have hp := prefix_mono first second scalar indices steps
  have hw := loop_bound first second scalar indices
  omega

theorem prefix_width {n m : ℕ} (first : Store n) (second : Store m) (scalar : SignedWord)
    (indices : List (List Bool)) (steps : ℕ) :
    binaryWordWidth (BinaryPhysicalInterpolationMeasured.loopWithExtras first second scalar (indices.take steps)).2 ≤
      binaryWordWidth (155*(BinaryPhysicalInterpolationMeasured.loopWithExtras first second scalar indices).1.2) :=
  binaryWordWidth_mono (prefix_bound first second scalar indices steps)

end Blotto.BinaryReturnedInterpolationExtras
