import Blotto.BinaryScalarTape
import Blotto.BinaryWordGroupLifetime

/-! Successful actual group rows inherit canonical words and source heights
through exact native/partial-run refinement. No row-height oracle is supplied. -/
namespace Blotto.BinaryWordGroupResult
open BinaryRationalNormalization BinaryRationalEncoding BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork
set_option maxHeartbeats 1500000

theorem uniform_success {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (row : FixedArrayTable m SignedWord)
    (h : (BinaryWordGroupLifetime.uniformRun store input hC hAd hm K scalar pc hp).1.1 = some row) :
    (BinaryGroupPartialRun.uniformRun input hC hAd hm K store.cap.value scalar
      (BinaryWordIndexCoinController.reader store) pc.value hp).1 = some row := by
  have hNative : (BinaryPRGWordControllerTerminal.uniformRun store input hC hAd hm K scalar pc hp).1 = some row := by
    rw [← BinaryWordGroupLifetime.uniformRun_erasure]
    exact h
  have hState := congrArg Prod.fst (BinaryPRGWordControllerTerminal.uniformRun_state store input hC hAd hm K scalar pc hp)
  exact hState.symm.trans hNative

theorem uniform_canonical {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (row : FixedArrayTable m SignedWord)
    (h : (BinaryWordGroupLifetime.uniformRun store input hC hAd hm K scalar pc hp).1.1 = some row) : ∀ j,CanonicalWord (row.read j) :=
  BinaryGroupPartialRun.uniformRun_canonical input hC hAd hm K store.cap.value scalar
    (BinaryWordIndexCoinController.reader store) pc.value hp row (uniform_success store input hC hAd hm K scalar pc hp row h)

theorem uniform_height {m : ℕ} (store : BinarySeedLookupTree.Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (s : ℕ) (hs : 2 ≤ s) (hHeight : UniformHeights input s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (row : FixedArrayTable m SignedWord)
    (h : (BinaryWordGroupLifetime.uniformRun store input hC hAd hm K scalar pc hp).1.1 = some row) :
    ∀ j,RationalHeight (value (row.read j)) (expressionHeightBudget (max s (K + 2)) 21) :=
  BinaryGroupReachedHeight.uniform_success_height input hC hAd hm s hs hHeight K store.cap.value scalar
    (BinaryWordIndexCoinController.reader store) pc.value hp row (uniform_success store input hC hAd hm K scalar pc hp row h)

theorem mixedTwo_success (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (row : FixedArrayTable 3 SignedWord)
    (h : (BinaryWordGroupLifetime.mixedTwoRun store input hC hAd K scalar pc hp).1.1 = some row) :
    (BinaryGroupPartialRun.mixedRun input hC hAd (Or.inl rfl) K store.cap.value scalar scalar
      (BinaryWordIndexCoinController.reader store) pc.value hp).1 = some row := by
  have hNative : (BinaryPRGWordControllerTerminal.mixedRun store input hC hAd (Or.inl rfl) K scalar scalar pc hp).1 = some row := by
    change (BinaryPRGWordControllerSegment.run store (mixedTwoPrepared input hC hAd) 0 K scalar pc hp).1 = some row
    rw [← BinaryWordGroupLifetime.mixedTwoRun_erasure]
    exact h
  have hState := congrArg Prod.fst (BinaryPRGWordControllerTerminal.mixedRun_state store input hC hAd (Or.inl rfl) K scalar scalar pc hp)
  exact hState.symm.trans hNative

theorem mixedTwo_canonical (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (K : ℕ) (scalar : BinaryScalarTape K)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (row : FixedArrayTable 3 SignedWord)
    (h : (BinaryWordGroupLifetime.mixedTwoRun store input hC hAd K scalar pc hp).1.1 = some row) : ∀ j,CanonicalWord (row.read j) :=
  BinaryGroupPartialRun.mixedRun_canonical input hC hAd (Or.inl rfl) K store.cap.value scalar scalar
    (BinaryWordIndexCoinController.reader store) pc.value hp row (mixedTwo_success store input hC hAd K scalar pc hp row h)

theorem mixedTwo_height (store : BinarySeedLookupTree.Store) (input : MixedInput 2) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (s : ℕ) (hs : 2 ≤ s) (hHeight : MixedHeights input s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (row : FixedArrayTable 3 SignedWord)
    (h : (BinaryWordGroupLifetime.mixedTwoRun store input hC hAd K scalar pc hp).1.1 = some row) :
    ∀ j,RationalHeight (value (row.read j)) (expressionHeightBudget (max s (K + 2)) 72) :=
  BinaryGroupReachedHeight.mixed_success_height input hC hAd (Or.inl rfl) s hs hHeight K store.cap.value scalar scalar
    (BinaryWordIndexCoinController.reader store) pc.value hp row (mixedTwo_success store input hC hAd K scalar pc hp row h)

end Blotto.BinaryWordGroupResult
