import Blotto.BinaryPRGNumericalFlattenLength
import Blotto.BinaryPRGCheckedGameLifetime

/-! Original game-frame bounds for the selected numerical flatten loops. -/
namespace Blotto.BinaryPRGNumericalFlattenLength
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGPreparation BinaryPRGRecognition BinaryPRGNumericalPreparationLifetime
open BinaryLifetimeFlattenControl
set_option autoImplicit false
set_option maxHeartbeats 1000000

def rawFlattenBound (length : ℕ) : ℕ :=
  4 * length * BinaryQuadraticLifetime.opcodeBound (3*(length+2)+1)

theorem rawFlattenBound_polynomial (length : ℕ) :
    rawFlattenBound length ≤ 21600000*(length+4)^4 := by
  calc
    rawFlattenBound length = 800000*length*(3*length+9)^3 := by
      unfold rawFlattenBound BinaryQuadraticLifetime.opcodeBound
      ring
    _ ≤ 800000*(length+4)*(3*(length+4))^3 := by
      gcongr <;> omega
    _ = 21600000*(length+4)^4 := by ring

theorem parsed_numerical_payload_bound (bits : List Bool)
    (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (h : (BinaryPRGGameFrameLifetime.readWithTrace bits).1 = some parsed) :
    let input := parsed.1.2.game.input
    let rows := parsed.1.2.rows
    let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
    let lengthEntries := BinaryLifetimeArray.mapDirect
      (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
    let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
      BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
    payloadCount (BinaryLifetimeArray.mapDirect Prod.snd lengthEntries) +
      payloadCount (BinaryLifetimeArray.mapDirect Prod.snd poorEntries) ≤
        rawFlattenBound bits.length := by
  dsimp only
  let input := parsed.1.2.game.input
  let rows := parsed.1.2.rows
  let n := parsed.1.1
  have hSize := BinaryPRGCheckedGameLifetime.parsed_sizes bits parsed h
  have hLength := length_entries_payload_bound input rows parsed.1.2.rows_readback
  have hPoor := poor_entries_payload_bound input parsed.1.2.game.canonical rows
    parsed.1.2.rows_readback
  have hWidth : widthBound input ≤ 3*(bits.length+2)+1 := by
    dsimp [widthBound,input]
    omega
  have hOp : BinaryQuadraticLifetime.opcodeBound (widthBound input) ≤
      BinaryQuadraticLifetime.opcodeBound (3*(bits.length+2)+1) := by
    unfold BinaryQuadraticLifetime.opcodeBound
    gcongr
  have hOne : n * (2 * BinaryQuadraticLifetime.opcodeBound (widthBound input)) ≤
      bits.length * (2 * BinaryQuadraticLifetime.opcodeBound (3*(bits.length+2)+1)) :=
    Nat.mul_le_mul hSize.1 (Nat.mul_le_mul_left 2 hOp)
  dsimp only [input,rows,n] at hLength hPoor hOne
  unfold rawFlattenBound
  calc
    _ ≤ 2 * (parsed.1.1 * (2 * BinaryQuadraticLifetime.opcodeBound
        (widthBound parsed.1.2.game.input))) := by
      omega
    _ ≤ 2 * (bits.length * (2 * BinaryQuadraticLifetime.opcodeBound (3*(bits.length+2)+1))) :=
      Nat.mul_le_mul_left 2 hOne
    _ = 4 * bits.length * BinaryQuadraticLifetime.opcodeBound (3*(bits.length+2)+1) := by ring

theorem parsed_numerical_flatten_visits (bits : List Bool)
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
    (flattenWithCount lengthLists #[]).2 +
      ((NativeArrayConversionCore.read (flattenWithCount lengthLists #[]).1).2.filterMap
        NativeArrayConversionCore.ReadSnapshot.readIndex).length + parsed.1.1 +
    (flattenWithCount poorLists #[]).2 +
      ((NativeArrayConversionCore.read (flattenWithCount poorLists #[]).1).2.filterMap
        NativeArrayConversionCore.ReadSnapshot.readIndex).length + parsed.1.1 ≤
      2*bits.length + 2*rawFlattenBound bits.length := by
  dsimp only
  let input := parsed.1.2.game.input
  let rows := parsed.1.2.rows
  let n := parsed.1.1
  let ratio := BinaryQuadraticLifetime.applyWithTrace .div input.b input.a
  let lengthEntries := BinaryLifetimeArray.mapDirect
    (BinaryQuadraticLifetime.applyWithTrace .mul two) rows
  let poorEntries := BinaryLifetimeArray.mapDirect (fun item =>
    BinaryQuadraticLifetime.applyWithTrace .mul ratio.1 item.1) lengthEntries
  have hLen : lengthEntries.length = n := by
    dsimp only [lengthEntries]
    rw [BinaryLifetimeArray.mapDirect_length,parsed.1.2.rows_length]
  have hPoor : poorEntries.length = n := by
    dsimp only [poorEntries]
    rw [BinaryLifetimeArray.mapDirect_length,hLen]
  have hFirst := fromEntries_flatten_visits n lengthEntries hLen
  have hSecond := fromEntries_flatten_visits n poorEntries hPoor
  have hPayload := parsed_numerical_payload_bound bits parsed h
  have hSize := (BinaryPRGCheckedGameLifetime.parsed_sizes bits parsed h).1
  dsimp only [input,rows,n,ratio,lengthEntries,poorEntries] at hFirst hSecond hPayload
  omega

theorem parsed_numerical_direct_flatten_visits (bits : List Bool)
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
    (BinaryLifetimeFlattenList.gatherWithCount lengthLists []).2 +
      lengthLists.length +
    (BinaryLifetimeFlattenList.gatherWithCount poorLists []).2 +
      poorLists.length ≤
        2*rawFlattenBound bits.length + 2*bits.length := by
  dsimp only
  have hPayload := parsed_numerical_payload_bound bits parsed h
  have hSizes := (BinaryPRGCheckedGameLifetime.parsed_sizes bits parsed h).1
  have hLength : (BinaryLifetimeArray.mapDirect Prod.snd
      (BinaryLifetimeArray.mapDirect
        (BinaryQuadraticLifetime.applyWithTrace .mul two) parsed.1.2.rows)).length =
      parsed.1.1 := by
    rw [BinaryLifetimeArray.mapDirect_length,BinaryLifetimeArray.mapDirect_length,
      parsed.1.2.rows_length]
  have hPoor : (BinaryLifetimeArray.mapDirect Prod.snd
      (BinaryLifetimeArray.mapDirect (fun item =>
        BinaryQuadraticLifetime.applyWithTrace .mul
          (BinaryQuadraticLifetime.applyWithTrace .div
            parsed.1.2.game.input.b parsed.1.2.game.input.a).1 item.1)
        (BinaryLifetimeArray.mapDirect
          (BinaryQuadraticLifetime.applyWithTrace .mul two) parsed.1.2.rows))).length =
      parsed.1.1 := by
    rw [BinaryLifetimeArray.mapDirect_length,BinaryLifetimeArray.mapDirect_length,
      BinaryLifetimeArray.mapDirect_length,parsed.1.2.rows_length]
  dsimp only at hPayload
  rw [BinaryLifetimeFlattenList.gatherWithCount_count,
    BinaryLifetimeFlattenList.gatherWithCount_count,hLength,hPoor]
  simp only [List.length_nil,Nat.add_zero,BinaryLifetimeFlattenList.payloadCount,
    payloadCount] at hPayload ⊢
  omega

end Blotto.BinaryPRGNumericalFlattenLength
