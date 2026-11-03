import Blotto.BinaryPRGHeapGroupWork
import Blotto.BinaryPRGWordControllerTerminalWork

/-! Every terminal regime uses the physical reflected continuation when it
reaches that branch. Emission consumes the exact retained group result. -/

namespace Blotto.BinaryPRGHeapTerminalWork
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryCachedTerminalPreparation BinaryCachedTerminalPromises BinaryCachedThreeDescriptorWork
open BinaryGroupRouteEmissionWork

def runPrepared {n : ℕ} (store : Store) {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerTerminal.Result store n × ℕ :=
  match hs : prepared.pivot with
  | none =>
      let drawn := BinaryPRGWordControllerGroupWork.uniformRun store prepared.uniform (prepared.uniform_canonical hC)
        (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hs)
        (prepared.count_bound hC hAd) K scalar pc hp
      let emitted := emitOptionWithWork prepared.routes drawn.1.1
      ((emitted.1,drawn.1.2),drawn.2 + emitted.2 + n * (n + 1) + 6 * n + 2)
  | some selected =>
      let drawn := BinaryPRGHeapGroupWork.mixedRun store prepared.mixed (prepared.mixed_canonical hC selected hs)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hs)
        (prepared.count_bound hC hAd) K outer scalar pc hp
      let emitted := emitMixedOptionWithWork prepared.routes selected drawn.1.1
      ((emitted.1,drawn.1.2),drawn.2 + emitted.2 + n * (n + 1) + 6 * n + 2)

theorem runPrepared_erasure {n : ℕ} (store : Store) {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runPrepared store prepared hC hAd K outer scalar pc hp).1 =
      BinaryPRGWordControllerTerminal.runPrepared store prepared hC hAd K outer scalar pc hp := by
  unfold runPrepared BinaryPRGWordControllerTerminal.runPrepared
  dsimp only
  split
  · rename_i hNone
    rw [emitOptionWithWork_state,BinaryPRGWordControllerGroupWork.uniformRun_erasure]
    all_goals
      split
      · rfl
      · rename_i selected hSome
        cases hNone.symm.trans hSome
  · rename_i selected hSome
    rw [emitMixedOptionWithWork_state,BinaryPRGHeapGroupWork.mixedRun_erasure]
    all_goals
      split
      · rename_i hNone
        cases hSome.symm.trans hNone
      · rename_i other hOther
        have he : selected = other := Option.some.inj (hSome.symm.trans hOther)
        subst other
        rfl

theorem runPrepared_cost_le {n : ℕ} (store : Store) {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (s : ℕ) (hs : 3 ≤ s)
    (hM : ∀ selected,prepared.pivot = some selected → MixedHeights prepared.mixed s)
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runPrepared store prepared hC hAd K outer scalar pc hp).2 ≤
      (BinaryPRGWordControllerTerminalWork.runPrepared store prepared hC hAd K outer scalar pc hp).2 +
        BinaryPRGHeapReflectedSetup.bound s store.width store.cap.value := by
  unfold runPrepared BinaryPRGWordControllerTerminalWork.runPrepared
  dsimp only
  split
  · rename_i hNone
    split
    · omega
    · rename_i selected hSome
      cases hNone.symm.trans hSome
  · rename_i selected hSome
    have hCost := BinaryPRGHeapGroupWork.mixedRun_cost_le store prepared.mixed
      (prepared.mixed_canonical hC selected hSome)
      (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hSome)
      (prepared.count_bound hC hAd) s hs (hM selected hSome) K outer scalar pc hp
    have hData := (BinaryPRGHeapGroupWork.mixedRun_erasure store prepared.mixed
      (prepared.mixed_canonical hC selected hSome)
      (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hSome)
      (prepared.count_bound hC hAd) K outer scalar pc hp).trans
        (BinaryPRGWordControllerGroupWork.mixedRun_erasure store prepared.mixed
          (prepared.mixed_canonical hC selected hSome)
          (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hSome)
          (prepared.count_bound hC hAd) K outer scalar pc hp).symm
    split
    · rename_i hNone
      cases hSome.symm.trans hNone
    · rename_i other hOther
      have he : selected = other := Option.some.inj (hSome.symm.trans hOther)
      subst other
      simp only [hData]
      omega

end Blotto.BinaryPRGHeapTerminalWork
