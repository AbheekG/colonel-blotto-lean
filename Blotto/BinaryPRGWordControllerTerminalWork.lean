import Blotto.BinaryPRGWordControllerGroupWork
import Blotto.BinaryCachedTerminalEmissionRun

/-! The terminal uses the actual concrete Store group draw and actual original
route emitter on the reached row.  Only the emitter's identical operand words
are transported to its source height theorem; another draw backend's cost is
not transported.  All four terminal regimes and failures are included. -/

namespace Blotto.BinaryPRGWordControllerTerminalWork
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryCachedTerminalPreparation BinaryCachedTerminalPromises BinaryCachedThreeDescriptorWork
open BinaryGroupRouteEmissionWork

theorem uniform_row_state {m : ℕ} (store : Store) (input : BinaryGroupInputs.UniformInput m) (hC : input.Canonical)
    (hAd : BinaryGroupSamplers.UniformAdmissible input) (hm : m = 2 ∨ m = 3)
    (K : ℕ) (scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerGroupWork.uniformRun store input hC hAd hm K scalar pc hp).1.1 =
      (BinaryGroupRetainedPrimitiveRun.uniformRun input hC hAd hm K store.cap.value scalar
        (BinaryWordIndexCoinController.reader store) pc.value hp).1.1 := by
  have hNew := congrArg Prod.fst (BinaryPRGWordControllerGroupWork.uniformRun_erasure store input hC hAd hm K scalar pc hp)
  have hController := congrArg Prod.fst (BinaryPRGWordControllerTerminal.uniformRun_state store input hC hAd hm K scalar pc hp)
  have hOld := congrArg Prod.fst (BinaryGroupRetainedPrimitiveRun.uniformRun_state input hC hAd hm K store.cap.value scalar
    (BinaryWordIndexCoinController.reader store) pc.value hp)
  exact hNew.trans (hController.trans hOld.symm)

theorem mixed_row_state {m : ℕ} (store : Store) (input : BinaryGroupInputs.MixedInput m) (hC : input.Canonical)
    (hAd : BinaryGroupSamplers.MixedAdmissible input) (hm : m = 2 ∨ m = 3)
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (BinaryPRGWordControllerGroupWork.mixedRun store input hC hAd hm K outer scalar pc hp).1.1 =
      (BinaryGroupRetainedPrimitiveRun.mixedRun input hC hAd hm K store.cap.value outer scalar
        (BinaryWordIndexCoinController.reader store) pc.value hp).1.1 := by
  have hNew := congrArg Prod.fst (BinaryPRGWordControllerGroupWork.mixedRun_erasure store input hC hAd hm K outer scalar pc hp)
  have hController := congrArg Prod.fst (BinaryPRGWordControllerTerminal.mixedRun_state store input hC hAd hm K outer scalar pc hp)
  have hOld := congrArg Prod.fst (BinaryGroupRetainedPrimitiveRun.mixedRun_state input hC hAd hm K store.cap.value outer scalar
    (BinaryWordIndexCoinController.reader store) pc.value hp)
  exact hNew.trans (hController.trans hOld.symm)

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
      ((emitted.1, drawn.1.2), drawn.2 + emitted.2 + n * (n + 1) + 6 * n + 2)
  | some selected =>
      let drawn := BinaryPRGWordControllerGroupWork.mixedRun store prepared.mixed (prepared.mixed_canonical hC selected hs)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hs)
        (prepared.count_bound hC hAd) K outer scalar pc hp
      let emitted := emitMixedOptionWithWork prepared.routes selected drawn.1.1
      ((emitted.1, drawn.1.2), drawn.2 + emitted.2 + n * (n + 1) + 6 * n + 2)

theorem runPrepared_erasure {n : ℕ} (store : Store) {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runPrepared store prepared hC hAd K outer scalar pc hp).1 =
      BinaryPRGWordControllerTerminal.runPrepared store prepared hC hAd K outer scalar pc hp := by
  unfold runPrepared BinaryPRGWordControllerTerminal.runPrepared
  dsimp only
  split
  · rename_i hNone
    rw [emitOptionWithWork_state, BinaryPRGWordControllerGroupWork.uniformRun_erasure]
    all_goals
      split
      · rfl
      · rename_i selected hSome
        cases hNone.symm.trans hSome
  · rename_i selected hSome
    rw [emitMixedOptionWithWork_state, BinaryPRGWordControllerGroupWork.mixedRun_erasure]
    all_goals
      split
      · rename_i hNone
        cases hSome.symm.trans hNone
      · rename_i other hOther
        have he : selected = other := Option.some.inj (hSome.symm.trans hOther)
        subst other
        rfl

theorem uniformBound_dimension_mono {first second : ℕ} (h : first ≤ second) (s K indexWidth remaining : ℕ) :
    BinaryPRGWordControllerGroupWork.uniformBound first s K indexWidth remaining ≤
      BinaryPRGWordControllerGroupWork.uniformBound second s K indexWidth remaining := by
  unfold BinaryPRGWordControllerGroupWork.uniformBound BinaryPRGWordControllerWork.segmentBound
    BinaryPRGWordControllerWork.pointBound
  gcongr

def bound (n s K indexWidth remaining : ℕ) : ℕ :=
  BinaryPRGWordControllerGroupWork.uniformBound 3 s K indexWidth remaining +
    BinaryPRGWordControllerGroupWork.mixedBound s K indexWidth remaining +
      BinaryCachedTerminalEmissionRun.emissionBound n s K + n * (n + 1) + 6 * n + 2

theorem runPrepared_bound {n : ℕ} (store : Store) {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hU : UniformHeights prepared.uniform s)
    (hM : ∀ selected, prepared.pivot = some selected → MixedHeights prepared.mixed s)
    (hR : ∀ j, RationalHeight (value (prepared.routes.read j).2) (expressionHeightBudget s 1))
    (K : ℕ) (outer scalar : Fin K → Bool) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runPrepared store prepared hC hAd K outer scalar pc hp).2 ≤ bound n s K store.width (store.cap.value - pc.value) := by
  have hm := prepared.count_bound hC hAd
  have hm3 : prepared.count ≤ 3 := by rcases hm with h | h <;> omega
  unfold runPrepared
  dsimp only
  split
  · rename_i hNone
    have hDraw := (BinaryPRGWordControllerGroupWork.uniformRun_bound store prepared.uniform (prepared.uniform_canonical hC)
      (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hNone) hm s hs hU K scalar pc hp).trans
      (uniformBound_dimension_mono hm3 s K store.width (store.cap.value - pc.value))
    have hEmit := BinaryCachedTerminalEmissionRun.uniform_emission_bound prepared.routes prepared.uniform (prepared.uniform_canonical hC)
      (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hNone) hm
      (BinaryCachedTerminalPromises.Prepared.routes_canonical prepared hC) s hs hR hU
      K store.cap.value scalar (BinaryWordIndexCoinController.reader store) pc.value hp
    rw [← uniform_row_state store prepared.uniform (prepared.uniform_canonical hC)
      (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hNone) hm K scalar pc hp] at hEmit
    unfold bound
    omega
  · rename_i selected hSome
    have hDraw := BinaryPRGWordControllerGroupWork.mixedRun_bound store prepared.mixed (prepared.mixed_canonical hC selected hSome)
      (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hSome) hm s hs (hM selected hSome)
      K outer scalar pc hp
    have hEmit := BinaryCachedTerminalEmissionRun.mixed_emission_bound prepared.routes selected prepared.mixed
      (prepared.mixed_canonical hC selected hSome)
      (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hSome) hm
      (BinaryCachedTerminalPromises.Prepared.routes_canonical prepared hC) s hs hR (hM selected hSome)
      K store.cap.value outer scalar (BinaryWordIndexCoinController.reader store) pc.value hp
    rw [← mixed_row_state store prepared.mixed (prepared.mixed_canonical hC selected hSome)
      (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hSome) hm K outer scalar pc hp] at hEmit
    unfold bound
    omega

end Blotto.BinaryPRGWordControllerTerminalWork
