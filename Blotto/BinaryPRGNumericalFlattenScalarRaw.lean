import Blotto.BinaryLifetimeFlattenScalarExposure
import Blotto.BinaryPRGNumericalFlattenRaw

/-! The retained array-based numerical flatten reference has an
original-frame-derived push/read operand-width bound. The selected trace
assembly now uses `BinaryLifetimeFlattenList.flattenDirect`; this ledger
does not price that selected list backend or native reference transport. -/
namespace Blotto.BinaryPRGNumericalFlattenScalarRaw
open BinaryPRGNumericalFlattenLength BinaryLifetimeFlattenControl
open BinaryLifetimeFlattenScalarExposure
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGPreparation BinaryPRGRecognition
set_option autoImplicit false

theorem parsed_numerical_flatten_scalar_bits (bits : List Bool)
    (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (h : (BinaryPRGGameFrameLifetime.readWithTrace bits).1 = some parsed) :
    let input := parsed.1.2.game.input
    let rows := parsed.1.2.rows
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    let lengthLists := BinaryLifetimeArray.mapDirect Prod.snd lengthEntries
    let poorLists := BinaryLifetimeArray.mapDirect Prod.snd poorEntries
    selectedBits lengthLists + selectedBits poorLists ≤
      8*(rawFlattenBound bits.length+2)*binaryWordWidth (rawFlattenBound bits.length+1) := by
  dsimp only
  have hPayload := parsed_numerical_payload_bound bits parsed h
  dsimp only at hPayload
  exact pairBits_bound _ _ _ hPayload

theorem raw_scalar_polynomial (length : ℕ) :
    8*(rawFlattenBound length+2)*binaryWordWidth (rawFlattenBound length+1) ≤
      4000000000000000*(length+4)^8 := by
  let X := length+4
  let B := rawFlattenBound length
  have hX : 1 ≤ X^4 := by
    exact Nat.one_le_pow 4 X (by dsimp [X]; omega)
  have hB : B ≤ 21600000*X^4 := rawFlattenBound_polynomial length
  have hB2 : B+2 ≤ 21600002*X^4 := by omega
  have hWidth : binaryWordWidth (B+1) ≤ B+2 := by
    unfold binaryWordWidth
    exact Nat.add_le_add_right (Nat.log2_le_self (B+1)) 1
  change 8*(B+2)*binaryWordWidth (B+1) ≤ 4000000000000000*X^8
  calc
    _ ≤ 8*(B+2)*(B+2) := Nat.mul_le_mul_left _ hWidth
    _ ≤ 8*(21600002*X^4)^2 := by
      have hSq := Nat.pow_le_pow_left hB2 2
      nlinarith only [hSq]
    _ = 3732480691200032*X^8 := by ring
    _ ≤ 4000000000000000*X^8 :=
      Nat.mul_le_mul_right _ (by decide)

theorem parsed_numerical_flatten_scalar_polynomial (bits : List Bool)
    (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (h : (BinaryPRGGameFrameLifetime.readWithTrace bits).1 = some parsed) :
    let input := parsed.1.2.game.input
    let rows := parsed.1.2.rows
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    let lengthLists := BinaryLifetimeArray.mapDirect Prod.snd lengthEntries
    let poorLists := BinaryLifetimeArray.mapDirect Prod.snd poorEntries
    selectedBits lengthLists + selectedBits poorLists ≤
      4000000000000000*(bits.length+4)^8 := by
  exact (parsed_numerical_flatten_scalar_bits bits parsed h).trans
    (raw_scalar_polynomial bits.length)

end Blotto.BinaryPRGNumericalFlattenScalarRaw
