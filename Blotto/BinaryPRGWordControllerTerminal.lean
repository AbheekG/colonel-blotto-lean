import Blotto.BinaryPRGWordControllerFour
import Blotto.BinaryCachedTerminalRun

/-! All terminal group regimes use the same Boolean seed Store/cap and absolute
counter. The retained packing, routes and selected descriptor are consumed
directly; exact original rows, failure and positions are proved. Arithmetic
factory/route and physical-address/ownership contracts remain distinct. -/

namespace Blotto.BinaryPRGWordControllerTerminal
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedTerminalPreparation BinaryCachedTerminalPromises

abbrev Result (store : Store) (n : ℕ) := BinaryPRGWordControllerSegment.Result store n
abbrev decoded {n : ℕ} (store : Store) := @BinaryPRGWordControllerSegment.decoded n store

def uniformRun {m : ℕ} (store : Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result store m :=
  BinaryPRGWordControllerSegment.run store (uniformPrepared input hC hAd hm) 0 K scalar pc hp

theorem uniformRun_state {m : ℕ} (store : Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    decoded store (uniformRun store input hC hAd hm K scalar pc hp) =
      BinaryGroupPartialRun.uniformRun input hC hAd hm K store.cap.value scalar
        (BinaryWordIndexCoinController.reader store) pc.value hp :=
  BinaryPRGWordControllerSegment.run_state store _ 0 K scalar pc hp

def mixedRun {m : ℕ} (store : Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result store (m + 1) := by
  by_cases h2 : m = 2
  · subst m
    exact BinaryPRGWordControllerSegment.run store (mixedTwoPrepared input hC hAd) 0 K scalar pc hp
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact BinaryPRGWordControllerFour.restoredRun store (mixedFour input) (mixedFour_canonical input hC)
      (mixedFour_admissible input hC hAd) K outer scalar pc hp

theorem mixedRun_state {m : ℕ} (store : Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    decoded store (mixedRun store input hC hAd hm K outer scalar pc hp) =
      BinaryGroupPartialRun.mixedRun input hC hAd hm K store.cap.value outer scalar
        (BinaryWordIndexCoinController.reader store) pc.value hp := by
  rcases hm with rfl | rfl
  · exact BinaryPRGWordControllerSegment.run_state store _ 0 K scalar pc hp
  · exact BinaryPRGWordControllerFour.restoredRun_state store (mixedFour input)
      (mixedFour_canonical input hC) (mixedFour_admissible input hC hAd) K outer scalar pc hp

theorem uniformRun_position {m : ℕ} (store : Store) (input : UniformInput m) (hC : input.Canonical)
    (hAd : UniformAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (uniformRun store input hC hAd hm K scalar pc hp).2.value ∧
      (uniformRun store input hC hAd hm K scalar pc hp).2.value ≤ store.cap.value :=
  BinaryPRGWordControllerSegment.run_position store _ 0 K scalar pc hp

theorem mixedRun_position {m : ℕ} (store : Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (mixedRun store input hC hAd hm K outer scalar pc hp).2.value ∧
      (mixedRun store input hC hAd hm K outer scalar pc hp).2.value ≤ store.cap.value := by
  rcases hm with rfl | rfl
  · exact BinaryPRGWordControllerSegment.run_position store _ 0 K scalar pc hp
  · exact BinaryPRGWordControllerFour.restoredRun_position store (mixedFour input)
      (mixedFour_canonical input hC) (mixedFour_admissible input hC hAd) K outer scalar pc hp

def runPrepared {n : ℕ} (store : Store) {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) : Result store n :=
  match hs : prepared.pivot with
  | none =>
      let drawn := uniformRun store prepared.uniform (prepared.uniform_canonical hC)
        (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hs)
        (prepared.count_bound hC hAd) K scalar pc hp
      (drawn.1.map (BinaryGroupRoutes.emit prepared.routes),drawn.2)
  | some selected =>
      let drawn := mixedRun store prepared.mixed (prepared.mixed_canonical hC selected hs)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hs)
        (prepared.count_bound hC hAd) K outer scalar pc hp
      (drawn.1.map (BinaryGroupRoutes.emitMixed prepared.routes selected),drawn.2)

theorem runPrepared_state {n : ℕ} (store : Store) {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    decoded store (runPrepared store prepared hC hAd K outer scalar pc hp) =
      BinaryCachedTerminalRun.runPrepared prepared hC hAd K store.cap.value outer scalar
        (BinaryWordIndexCoinController.reader store) pc.value hp := by
  unfold runPrepared BinaryCachedTerminalRun.runPrepared
  dsimp only
  split
  · rename_i hs
    split
    · exact congrArg (fun result : Option (FixedArrayTable prepared.count SignedWord) × ℕ =>
        (result.1.map (BinaryGroupRoutes.emit prepared.routes),result.2))
        (uniformRun_state store prepared.uniform (prepared.uniform_canonical hC)
          (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hs)
          (prepared.count_bound hC hAd) K scalar pc hp)
    · rename_i selected hOther
      cases hs.symm.trans hOther
  · rename_i selected hs
    split
    · rename_i hOther
      cases hs.symm.trans hOther
    · rename_i other hOther
      have he : selected = other := Option.some.inj (hs.symm.trans hOther)
      subst other
      exact congrArg (fun result : Option (FixedArrayTable (prepared.count + 1) SignedWord) × ℕ =>
        (result.1.map (BinaryGroupRoutes.emitMixed prepared.routes selected),result.2))
        (mixedRun_state store prepared.mixed (prepared.mixed_canonical hC selected hs)
          (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hs)
          (prepared.count_bound hC hAd) K outer scalar pc hp)

theorem runPrepared_position {n : ℕ} (store : Store) {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (runPrepared store prepared hC hAd K outer scalar pc hp).2.value ∧
      (runPrepared store prepared hC hAd K outer scalar pc hp).2.value ≤ store.cap.value := by
  unfold runPrepared
  dsimp only
  split
  · exact uniformRun_position store _ _ _ _ K scalar pc hp
  · exact mixedRun_position store _ _ _ _ K outer scalar pc hp

end Blotto.BinaryPRGWordControllerTerminal
