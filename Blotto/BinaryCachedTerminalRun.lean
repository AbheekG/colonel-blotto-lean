import Blotto.BinaryCachedTerminalPromises

/-! Terminal sampling executes from cached group count/totals/routes and pivot
words. Preparation is separate and reusable; no grouping is rebuilt by the
uniform/mixed group-input factories during a draw. Exact byte/position refinement
includes exhaustion, with no local fallback substituted for an outer failure. -/

namespace Blotto.BinaryCachedTerminalRun
open BinaryRationalNormalization BinaryRationalEncoding BinaryCachedTerminalPreparation BinaryCachedTerminalPromises

def runPrepared {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    Option (FixedArrayTable n SignedWord) × ℕ :=
  match hs : prepared.pivot with
  | none =>
      let sampled := BinaryGroupPartialRun.uniformRun prepared.uniform (prepared.uniform_canonical hC)
        (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hs)
        (prepared.count_bound hC hAd) K N scalar bits pos hp
      (sampled.1.map (BinaryGroupRoutes.emit prepared.routes), sampled.2)
  | some selected =>
      let sampled := BinaryGroupPartialRun.mixedRun prepared.mixed (prepared.mixed_canonical hC selected hs)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hs)
        (prepared.count_bound hC hAd) K N outer scalar bits pos hp
      (sampled.1.map (BinaryGroupRoutes.emitMixed prepared.routes selected), sampled.2)

theorem runPrepared_state {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    runPrepared prepared hC hAd K N outer scalar bits pos hp =
      BinaryTerminalPartialRun.runIndexed input hC hAd K N outer scalar bits pos hp := by
  unfold runPrepared BinaryTerminalPartialRun.runIndexed
  dsimp only
  split
  · rename_i hNone
    have hOld : BinaryTerminalGrouping.pivot input = none := prepared.pivot_eq.symm.trans hNone
    split
    · have hC' : (BinaryTerminalGroupInputs.castUniform prepared.count_eq prepared.uniform).Canonical := by
        rw [prepared.uniform_cast]
        exact BinaryTerminalGroupInputs.uniform_canonical input hC
      have hAd' : BinaryGroupSamplers.UniformAdmissible
          (BinaryTerminalGroupInputs.castUniform prepared.count_eq prepared.uniform) := by
        rw [prepared.uniform_cast]
        exact BinaryTerminalPromises.uniformAdmissible input hC hAd hOld
      have hRun := uniformRun_cast prepared.count_eq prepared.uniform (prepared.uniform_canonical hC)
        (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hNone)
        (prepared.count_bound hC hAd) hC' hAd'
        (BinaryTerminalPromises.groupCount input hC hAd) K N scalar bits pos hp
      simp only [prepared.uniform_cast] at hRun
      apply Prod.ext
      · rw [← congrArg Prod.fst hRun, Option.map_map, ← prepared.routes_cast]
        simp only [Function.comp_def, emit_cast]
      · exact congrArg (fun result : Option (FixedArrayTable (BinaryTerminalGrouping.groups input).length SignedWord) × ℕ =>
          result.2) hRun
    · rename_i selected hBad
      cases hOld.symm.trans hBad
  · rename_i selected hSome
    have hOld : BinaryTerminalGrouping.pivot input = some selected := prepared.pivot_eq.symm.trans hSome
    split
    · rename_i hBad
      cases hOld.symm.trans hBad
    · rename_i other hOther
      have he : selected = other := Option.some.inj (hOld.symm.trans hOther)
      subst other
      have hC' : (BinaryTerminalGroupInputs.castMixed prepared.count_eq prepared.mixed).Canonical := by
        rw [prepared.mixed_cast selected hSome]
        exact BinaryTerminalGroupInputs.mixed_canonical input hC selected
      have hAd' : BinaryGroupSamplers.MixedAdmissible
          (BinaryTerminalGroupInputs.castMixed prepared.count_eq prepared.mixed) := by
        rw [prepared.mixed_cast selected hSome]
        exact BinaryTerminalPromises.mixedAdmissible input hC hAd selected hOld
      have hRun := mixedRun_cast prepared.count_eq prepared.mixed (prepared.mixed_canonical hC selected hSome)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hSome)
        (prepared.count_bound hC hAd) hC' hAd'
        (BinaryTerminalPromises.groupCount input hC hAd) K N outer scalar bits pos hp
      simp only [prepared.mixed_cast selected hSome] at hRun
      apply Prod.ext
      · rw [← congrArg Prod.fst hRun, Option.map_map, ← prepared.routes_cast]
        simp only [Function.comp_def, emitMixed_cast]
      · exact congrArg (fun result : Option (FixedArrayTable ((BinaryTerminalGrouping.groups input).length + 1) SignedWord) × ℕ =>
          result.2) hRun

def runIndexed {n : ℕ} (input : BinaryTerminalGrouping.Input n) (hC : input.Canonical)
    (hAd : BinaryTerminalPromises.Admissible input) (K N : ℕ) (outer scalar : Fin K → Bool)
    (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) : Option (FixedArrayTable n SignedWord) × ℕ :=
  let prepared := BinaryCachedTerminalPreparation.prepare input
  runPrepared prepared hC hAd K N outer scalar bits pos hp

theorem runIndexed_state {n : ℕ} (input : BinaryTerminalGrouping.Input n) (hC : input.Canonical)
    (hAd : BinaryTerminalPromises.Admissible input) (K N : ℕ) (outer scalar : Fin K → Bool)
    (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    runIndexed input hC hAd K N outer scalar bits pos hp =
      BinaryTerminalPartialRun.runIndexed input hC hAd K N outer scalar bits pos hp :=
  runPrepared_state _ _ _ _ _ _ _ _ _ _

theorem runPrepared_canonical {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N)
    (row : FixedArrayTable n SignedWord) (h : (runPrepared prepared hC hAd K N outer scalar bits pos hp).1 = some row) :
    ∀ j, CanonicalWord (row.read j) := by
  rw [runPrepared_state] at h
  exact BinaryTerminalPartialRun.runIndexed_canonical input hC hAd K N outer scalar bits pos hp row h

theorem runPrepared_position {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    pos ≤ (runPrepared prepared hC hAd K N outer scalar bits pos hp).2 ∧
      (runPrepared prepared hC hAd K N outer scalar bits pos hp).2 ≤ N := by
  rw [runPrepared_state]
  exact BinaryTerminalPartialRun.runIndexed_position input hC hAd K N outer scalar bits pos hp

end Blotto.BinaryCachedTerminalRun
