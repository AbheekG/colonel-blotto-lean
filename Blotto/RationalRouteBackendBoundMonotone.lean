import Blotto.RationalPRGRequestRouteBackendWork

/-! Cost envelopes increase with verified input field/word/slot bounds.
These monotonicity statements concern envelope formulas, not the actual natural
primitive price function. The existing primitive hypotheses stay unchanged. -/

namespace Blotto.FixedWordRegion

theorem addressWidth_mono {base n W Base N V : ℕ} (hb : base ≤ Base) (hn : n ≤ N) (hW : W ≤ V) :
    addressWidth base n W ≤ addressWidth Base N V := by
  apply binaryWordWidth_mono
  exact Nat.add_le_add_right (Nat.add_le_add hb (Nat.mul_le_mul hn hW)) 1

theorem accessBound_mono (c : ℕ) {base n W Base N V : ℕ} (hb : base ≤ Base) (hn : n ≤ N) (hW : W ≤ V) :
    accessBound c base n W ≤ accessBound c Base N V :=
  Nat.add_le_add_right (Nat.mul_le_mul_left _ (addressWidth_mono hb hn hW)) 6

end Blotto.FixedWordRegion

namespace Blotto.BinaryAddressFormation

theorem operandBound_mono (c : ℕ) : Monotone (operandBound c) := by
  intro a b hab
  have hLoop := indexedLoopMetadataBound_mono c hab
  unfold operandBound
  gcongr

theorem workBound_mono : Monotone workBound := by
  intro a b hab
  unfold workBound
  gcongr

theorem encodedWorkBound_mono (c : ℕ) {base n W Base N V : ℕ} (hb : base ≤ Base) (hn : n ≤ N) (hW : W ≤ V) :
    encodedWorkBound c base n W ≤ encodedWorkBound c Base N V := by
  have hAddress := FixedWordRegion.addressWidth_mono hb hn hW
  exact Nat.add_le_add (Nat.mul_le_mul_left 4 (operandBound_mono c hAddress)) (workBound_mono hAddress)

end Blotto.BinaryAddressFormation

namespace Blotto.FixedWordRegion

theorem formedAccessBound_mono (c : ℕ) {n W N V : ℕ} (hn : n ≤ N) (hW : W ≤ V) :
    formedAccessBound c n W ≤ formedAccessBound c N V :=
  Nat.add_le_add (BinaryAddressFormation.encodedWorkBound_mono c (le_refl 0) hn hW)
    (accessBound_mono c (le_refl 0) hn hW)

end Blotto.FixedWordRegion

namespace Blotto.RationalTerminalPacking

theorem routePayloadWidth_mono {n s N t : ℕ} (hn : n ≤ N) (hs : s ≤ t) : routePayloadWidth n s ≤ routePayloadWidth N t := by
  have hWidth := binaryWordWidth_mono (Nat.add_le_add_right hn 4)
  unfold routePayloadWidth
  omega

end Blotto.RationalTerminalPacking

namespace Blotto.BinaryRouteFrame

theorem encodingBound_mono (c : ℕ) : Monotone (encodingBound c) := by
  intro a b hab
  have hMeta := BinaryNatFrame.encodingMetadataBound_mono c hab
  unfold encodingBound
  gcongr

theorem decodingBound_mono_length (model : RationalCostModel) (c m : ℕ) : Monotone (decodingBound model c m) := by
  intro a b hab
  have hPrice := model.monotone (show 4 * a + 13 ≤ 4 * b + 13 by omega)
  unfold decodingBound
  gcongr

end Blotto.BinaryRouteFrame

namespace Blotto.BinaryRouteSlot

theorem preparationBound_mono (c : ℕ) {P W Q V : ℕ} (hP : P ≤ Q) (hW : W ≤ V) :
    preparationBound c P W ≤ preparationBound c Q V := by
  have hEncode := BinaryRouteFrame.encodingBound_mono c hP
  have hLoop := indexedLoopMetadataBound_mono c hW
  unfold preparationBound
  gcongr

theorem readingBound_mono (model : RationalCostModel) (c m : ℕ) {n W N V : ℕ} (hn : n ≤ N) (hW : W ≤ V) :
    readingBound model c n m W ≤ readingBound model c N m V := by
  have hAddress := FixedWordRegion.accessBound_mono c (le_refl 0) hn hW
  have hLoop := indexedLoopMetadataBound_mono c hW
  have hDecode := BinaryRouteFrame.decodingBound_mono_length model c m hW
  have hMeta := BinaryRouteFrame.naturalMetadataBound_mono c hW
  unfold readingBound
  gcongr

end Blotto.BinaryRouteSlot

namespace Blotto.RationalTerminalPacking

theorem routeBitBuildBound_mono (c : ℕ) {n s W A N t V B : ℕ} (hn : n ≤ N) (hs : s ≤ t) (hW : W ≤ V) (hA : A ≤ B) :
    routeBitBuildBound c n s W A ≤ routeBitBuildBound c N t V B := by
  have hPrepare := BinaryRouteSlot.preparationBound_mono c (routePayloadWidth_mono hn hs) hW
  have hAddress := FixedWordRegion.addressWidth_mono (le_refl 0) hn hW
  have hRecords := indexedLoopMetadataBound_mono c (Nat.mul_le_mul_left 2 hn)
  have hBits := indexedLoopMetadataBound_mono c (show 2 * n * W ≤ 2 * N * V by gcongr)
  unfold routeBitBuildBound
  gcongr

end Blotto.RationalTerminalPacking

namespace Blotto.RationalTerminalLotto

theorem terminalRouteBackendBound_mono (model : RationalCostModel) (c : ℕ) {n s W N t V : ℕ}
    (hn : n ≤ N) (hs : s ≤ t) (hW : W ≤ V) :
    terminalRouteBackendBound model c n s W ≤ terminalRouteBackendBound model c N t V := by
  have hBuild := RationalTerminalPacking.routeBitBuildBound_mono c hn hs hW (FixedWordRegion.formedAccessBound_mono c hn hW)
  have hRead := BinaryRouteSlot.readingBound_mono model c 3 hn hW
  have hForm := BinaryAddressFormation.encodedWorkBound_mono c (le_refl 0) hn hW
  unfold terminalRouteBackendBound routeReadFormationBound
  gcongr

end Blotto.RationalTerminalLotto

namespace Blotto.RationalLottoResourceSystem

theorem bitRouteSlotWidth_mono {n s N t : ℕ} (hn : n ≤ N) (hs : s ≤ t) : bitRouteSlotWidth n s ≤ bitRouteSlotWidth N t :=
  Nat.add_le_add_right (Nat.mul_le_mul_left 2 (RationalTerminalPacking.routePayloadWidth_mono hn hs)) 1

end Blotto.RationalLottoResourceSystem
