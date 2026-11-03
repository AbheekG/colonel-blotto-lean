import Blotto.BinaryPRGCheckedPhysicalPreparationMeasured
import Blotto.BinaryPRGNumericalFlattenRaw
import Blotto.BinaryTerminalPhysicalRawPolynomial

/-! Original measured game-frame output derives actual numerical map,
compatibility pack/flatten and physical-store work. No caller supplies entry
widths or an accepted-promise assumption. Old traces transfer retained-prefix
bounds; native observer/address/reference/allocator realisation remains open. -/
namespace Blotto.BinaryPRGCheckedPhysicalPreparationBounds
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGCheckedPhysicalPreparationMeasured
set_option autoImplicit false
set_option maxHeartbeats 3000000

def rawPrice (L : ℕ) : ℕ := BinaryPRGNumericalEntriesMeasured.price L (L+2)+128*(L+1)^2+
  8*BinaryPRGNumericalFlattenLength.rawFlattenBound L+2*PRGPhysicalArrayInterface.preparationBound L+8*L+36

theorem prepare_raw_work (frame : List Bool) (parsed : (Σ n,BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (hParsed : (BinaryPRGGameFrameMeasured.read frame).1.1 = some parsed) :
    (prepare parsed.1.2.game.input parsed.1.2.rows parsed.1.2.rows_readback).2 ≤ rawPrice frame.length := by
  have hOld : (BinaryPRGGameFrameLifetime.readWithTrace frame).1 = some parsed :=
    (congrArg Prod.fst (BinaryPRGGameFrameMeasured.read_erases frame)).symm.trans hParsed
  let input := parsed.1.2.game.input
  let rows := parsed.1.2.rows
  let n := parsed.1.1
  let e := (BinaryPRGNumericalEntriesMeasured.prepare input rows parsed.1.2.rows_readback).1
  have hE : e = BinaryPRGNumericalEntriesMeasured.reference input rows parsed.1.2.rows_readback :=
    BinaryPRGNumericalEntriesMeasured.prepare_data input rows parsed.1.2.rows_readback
  have hSizes := BinaryPRGCheckedGameLifetime.parsed_sizes frame parsed hOld
  have hEW := (BinaryPRGNumericalEntriesMeasured.prepare_work input parsed.1.2.game.canonical rows parsed.1.2.rows_readback).trans
    (BinaryPRGNumericalEntriesMeasured.price_mono hSizes.1 hSizes.2)
  have hLP := BinaryLifetimeEntriesMeasured.fromEntries_work n e.lengths e.lengths_size
  have hPP := BinaryLifetimeEntriesMeasured.fromEntries_work n e.poor e.poor_size
  have hLS := BinaryPRGNumericalPhysicalMapMeasured.prepare_work e.lengths
  have hPS := BinaryPRGNumericalPhysicalMapMeasured.prepare_work e.poor
  have hEnv := BinaryPRGNumericalPhysicalEntries.parsed_pair_raw_envelopes frame parsed hOld
  have hEnvL : BinaryWordObjectArrayLifetime.envelope (BinaryPRGNumericalPhysicalEntries.words e.lengths) ≤
      PRGPhysicalArrayInterface.preparationBound frame.length := by
    rw [hE]
    exact hEnv.1
  have hEnvP : BinaryWordObjectArrayLifetime.envelope (BinaryPRGNumericalPhysicalEntries.words e.poor) ≤
      PRGPhysicalArrayInterface.preparationBound frame.length := by
    rw [hE]
    exact hEnv.2
  have hPayload : BinaryLifetimeFlattenList.payloadCount (BinaryLifetimeArray.mapDirect Prod.snd e.lengths)+
      BinaryLifetimeFlattenList.payloadCount (BinaryLifetimeArray.mapDirect Prod.snd e.poor) ≤
      BinaryPRGNumericalFlattenLength.rawFlattenBound frame.length := by
    rw [hE]
    exact BinaryPRGNumericalFlattenLength.parsed_numerical_payload_bound frame parsed hOld
  have hSq := Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left (Nat.add_le_add_right hSizes.1 1) 2)
  have hLSize := e.lengths_size
  have hPSize := e.poor_size
  change (BinaryPRGNumericalPhysicalMapMeasured.fixedPhysical n e.lengths e.lengths_size).2 ≤ _ at hLS
  change (BinaryPRGNumericalPhysicalMapMeasured.fixedPhysical n e.poor e.poor_size).2 ≤ _ at hPS
  rw [prepare_charge]
  change (BinaryPRGNumericalEntriesMeasured.prepare input rows parsed.1.2.rows_readback).2+
    (BinaryLifetimeEntriesMeasured.fromEntries n e.lengths e.lengths_size).2+
    (BinaryLifetimeEntriesMeasured.fromEntries n e.poor e.poor_size).2+
    (BinaryPRGNumericalPhysicalMapMeasured.fixedPhysical n e.lengths e.lengths_size).2+
    (BinaryPRGNumericalPhysicalMapMeasured.fixedPhysical n e.poor e.poor_size).2+16 ≤ _
  unfold rawPrice
  dsimp only [n] at hLP hPP hLSize hPSize hLS hPS ⊢
  omega

theorem rawPrice_polynomial (L : ℕ) : rawPrice L ≤ 1000000000*(L+4)^5 := by
  let X := L+4
  have hX : 0 < X := by dsimp [X]; omega
  have hEntry : BinaryPRGNumericalEntriesMeasured.price L (L+2) ≤ 1000000*X^3 := by
    unfold BinaryPRGNumericalEntriesMeasured.price BinaryPRGPromiseControlMeasured.opcodePrice
    dsimp only [X]
    ring_nf
    omega
  have hEntryTop := hEntry.trans (Nat.mul_le_mul_left 1000000 (Nat.pow_le_pow_right hX (by decide : 3 ≤ 5)))
  have hSquare : 128*(L+1)^2 ≤ 128*X^5 :=
    Nat.mul_le_mul_left 128 ((Nat.pow_le_pow_left (show L+1 ≤ X by dsimp [X]; omega) 2).trans
      (Nat.pow_le_pow_right hX (by decide : 2 ≤ 5)))
  have hFlat := (BinaryPRGNumericalFlattenLength.rawFlattenBound_polynomial L).trans
    (Nat.mul_le_mul_left 21600000 (Nat.pow_le_pow_right hX (by decide : 4 ≤ 5)))
  have hPhysical := BinaryTerminalPhysicalRawPolynomial.preparation_bound L
  have hLinear : L ≤ X^5 := (show L ≤ X by dsimp [X]; omega).trans
    (by simpa only [pow_one] using Nat.pow_le_pow_right hX (by decide : 1 ≤ 5))
  have hOne : 1 ≤ X^5 := Nat.one_le_pow 5 X (by omega)
  change PRGPhysicalArrayInterface.preparationBound L ≤ 100000000*X^5 at hPhysical
  unfold rawPrice
  change _ ≤ 1000000000*X^5
  omega

theorem checked_raw_work (frame : List Bool) (parsed : (Σ n,BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (hParsed : (BinaryPRGGameFrameMeasured.read frame).1.1 = some parsed) :
    (checked parsed.1.2.game.input parsed.1.2.game.canonical parsed.1.2.rows parsed.1.2.rows_readback).2 ≤
      4000000000*(frame.length+4)^5 := by
  have hParts := checked_work_parts parsed.1.2.game.input parsed.1.2.game.canonical
    parsed.1.2.rows parsed.1.2.rows_readback
  have hPrep := (prepare_raw_work frame parsed hParsed).trans (rawPrice_polynomial frame.length)
  have hCheck := BinaryPRGPromiseMeasured.parsed_work frame parsed hParsed
  have hX : 0 < frame.length+4 := by omega
  have hPow : (frame.length+1)^3 ≤ (frame.length+4)^5 :=
    (Nat.pow_le_pow_left (by omega : frame.length+1 ≤ frame.length+4) 3).trans
      (Nat.pow_le_pow_right hX (by decide : 3 ≤ 5))
  have hCheckTop := hCheck.trans (Nat.mul_le_mul_left 2000000000 hPow)
  have hOne : 1 ≤ (frame.length+4)^5 := Nat.one_le_pow 5 _ (by omega)
  omega

theorem prepare_raw_usage (frame : List Bool) (parsed : (Σ n,BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (hParsed : (BinaryPRGGameFrameMeasured.read frame).1.1 = some parsed) :
    usage (prepare parsed.1.2.game.input parsed.1.2.rows parsed.1.2.rows_readback).1.2 ≤
      BinaryPRGNumericalPreparationLifetime.envelope frame.length (frame.length+2)+
        2*(PRGPhysicalArrayInterface.preparationBound frame.length+2*frame.length+40)+136 := by
  rw [prepare_erases]
  exact BinaryPRGCheckedPhysicalPreparationLifetime.parsed_numerical_physical_usage frame parsed
    ((congrArg Prod.fst (BinaryPRGGameFrameMeasured.read_erases frame)).symm.trans hParsed)

theorem checked_raw_usage (frame : List Bool) (parsed : (Σ n,BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (hParsed : (BinaryPRGGameFrameMeasured.read frame).1.1 = some parsed) :
    usage (checked parsed.1.2.game.input parsed.1.2.game.canonical parsed.1.2.rows parsed.1.2.rows_readback).1.2 ≤
      BinaryPRGPromiseLifetime.envelope frame.length (frame.length+2)+
      BinaryPRGNumericalPreparationLifetime.envelope frame.length (frame.length+2)+
      2*(PRGPhysicalArrayInterface.preparationBound frame.length+2*frame.length+40)+256 := by
  rw [checked_erases]
  exact BinaryPRGCheckedPhysicalPreparationLifetime.parsed_checked_physical_usage frame parsed
    ((congrArg Prod.fst (BinaryPRGGameFrameMeasured.read_erases frame)).symm.trans hParsed)

theorem all_prefix (frame : List Bool) (parsed : (Σ n,BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (hParsed : (BinaryPRGGameFrameMeasured.read frame).1.1 = some parsed) (borrowed steps : ℕ) :
    retainedHeap (borrowed+frame.length)
        (checked parsed.1.2.game.input parsed.1.2.game.canonical parsed.1.2.rows parsed.1.2.rows_readback).1.2 steps ≤
      borrowed+frame.length+BinaryPRGPromiseLifetime.envelope frame.length (frame.length+2)+
        BinaryPRGNumericalPreparationLifetime.envelope frame.length (frame.length+2)+
        2*(PRGPhysicalArrayInterface.preparationBound frame.length+2*frame.length+40)+256 ∧
    framePeak ((checked parsed.1.2.game.input parsed.1.2.game.canonical parsed.1.2.rows parsed.1.2.rows_readback).1.2.take steps) ≤
      BinaryPRGPromiseLifetime.envelope frame.length (frame.length+2)+
        BinaryPRGNumericalPreparationLifetime.envelope frame.length (frame.length+2)+
        2*(PRGPhysicalArrayInterface.preparationBound frame.length+2*frame.length+40)+256 := by
  simpa only [Nat.add_assoc] using
    BinaryPRGHeapTraceUsage.all_prefix _ _ (checked_raw_usage frame parsed hParsed) (borrowed+frame.length) steps

end Blotto.BinaryPRGCheckedPhysicalPreparationBounds
