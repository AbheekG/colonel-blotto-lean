import Blotto.BinaryReflectedRunRefinement
import Blotto.BinaryReflectedCachedRun

/-! An indexed reflected entry point uses a suffix reader over the same input
buffer and returns the absolute consumed position. No bits are copied and no
coin cap is reset; only N-pos remaining bits are available to the full serial
runner. Exact indexed source semantics are proved. -/

namespace Blotto.BinaryReflectedIndexedRun
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedSerialRun BinaryReflectedSerialValue

def run (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    Option (FixedArrayTable 4 SignedWord) × ℕ :=
  let result := BinaryReflectedCachedRun.run input hC hAd K (N-pos) outer scalar
    (WordStateMachine.inputWindow bits pos (N-pos) (by omega))
  (result.1,pos+result.2)

theorem run_refines (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    ((run input hC hAd K N outer scalar bits pos hp).1.map sourceRow,(run input hC hAd K N outer scalar bits pos hp).2) =
      WordMappedIndexedRefinement.mapResult (RationalAffineAllocation.reflectAppend source.originalLengths).value
        (((source.reflectedResourceSystem hCase).machine K outer scalar).runCursorIndexed N bits
          (.state (source.reflectedResourceSystem hCase).samplingStart) pos hp) := by
  have he := BinaryReflectedRunRefinement.run_refines input source hC hr hCase hAd K (N-pos) outer scalar
    (WordStateMachine.inputWindow bits pos (N-pos) (by omega))
  rw [← BinaryReflectedCachedRun.run_eq] at he
  rw [((source.reflectedResourceSystem hCase).machine K outer scalar).runCursorIndexed_window N bits
    (.state (source.reflectedResourceSystem hCase).samplingStart) pos (N-pos) (by omega)]
  unfold run WordMappedIndexedRefinement.mapResult WordStateMachine.offsetConsumed
  have hRun := WordStateMachine.run_eq_numeric ((source.reflectedResourceSystem hCase).machine K outer scalar)
    (N-pos) (source.reflectedResourceSystem hCase).samplingStart (WordStateMachine.inputWindow bits pos (N-pos) (by omega))
  rw [WordStateMachine.runNumeric,WordStateMachine.runCursorIndexed_zero] at hRun
  rw [← hRun]
  exact congrArg (fun result : Option (Fin 4 → ℚ) × ℕ => (result.1,pos+result.2)) he

theorem run_position (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    pos ≤ (run input hC hAd K N outer scalar bits pos hp).2 ∧
      (run input hC hAd K N outer scalar bits pos hp).2 ≤ N := by
  have he := congrArg Prod.snd (run_refines input source hC hr hCase hAd K N outer scalar bits pos hp)
  rw [he]
  exact ((source.reflectedResourceSystem hCase).machine K outer scalar).runCursorIndexed_position_bounds N bits
    (.state (source.reflectedResourceSystem hCase).samplingStart) pos hp

theorem run_failure_iff (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (run input hC hAd K N outer scalar bits pos hp).1=none ↔
      (((source.reflectedResourceSystem hCase).machine K outer scalar).runCursorIndexed N bits
        (.state (source.reflectedResourceSystem hCase).samplingStart) pos hp).1=none := by
  have he := congrArg Prod.fst (run_refines input source hC hr hCase hAd K N outer scalar bits pos hp)
  have hn := congrArg (fun option => option=none) he
  simpa only [WordMappedIndexedRefinement.mapResult,Option.map_eq_none_iff] using Iff.of_eq hn

end Blotto.BinaryReflectedIndexedRun
