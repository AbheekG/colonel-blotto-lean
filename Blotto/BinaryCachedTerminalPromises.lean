import Blotto.BinaryCachedTerminalPreparation

/-! Cached group inputs receive canonicality, admissibility and the two/three
group count from the actual prepared terminal data. Group-size transports are
proof-only. Native uniform/mixed sampling and route emission preserve the
retained bytes and reader position under those transports. -/

namespace Blotto.BinaryCachedTerminalPromises
open BinaryRationalNormalization BinaryRationalEncoding BinaryCachedTerminalPreparation

theorem uniform_admissible_cast {m k : ℕ} (h : m = k) (input : BinaryGroupInputs.UniformInput m)
    (hAd : BinaryGroupSamplers.UniformAdmissible (BinaryTerminalGroupInputs.castUniform h input)) :
    BinaryGroupSamplers.UniformAdmissible input := by cases h; exact hAd

theorem mixed_admissible_cast {m k : ℕ} (h : m = k) (input : BinaryGroupInputs.MixedInput m)
    (hAd : BinaryGroupSamplers.MixedAdmissible (BinaryTerminalGroupInputs.castMixed h input)) :
    BinaryGroupSamplers.MixedAdmissible input := by cases h; exact hAd

theorem Prepared.uniform_admissible {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input) (h : prepared.pivot = none) :
    BinaryGroupSamplers.UniformAdmissible prepared.uniform := by
  apply uniform_admissible_cast prepared.count_eq
  rw [prepared.uniform_cast]
  exact BinaryTerminalPromises.uniformAdmissible input hC hAd (prepared.pivot_eq.symm.trans h)

theorem Prepared.mixed_admissible {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input) (selected : Fin n)
    (h : prepared.pivot = some selected) : BinaryGroupSamplers.MixedAdmissible prepared.mixed := by
  apply mixed_admissible_cast prepared.count_eq
  rw [prepared.mixed_cast selected h]
  exact BinaryTerminalPromises.mixedAdmissible input hC hAd selected (prepared.pivot_eq.symm.trans h)

theorem routes_canonical_cast {n m k : ℕ} (h : m = k) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (hC : ∀ j, CanonicalWord ((castRoutes h routes).read j).2) :
    ∀ j, CanonicalWord (routes.read j).2 := by cases h; exact hC

theorem Prepared.routes_canonical {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) : ∀ j, CanonicalWord (prepared.routes.read j).2 := by
  apply routes_canonical_cast prepared.count_eq
  rw [prepared.routes_cast]
  exact BinaryTerminalRoutes.prepare_canonical input hC

theorem castTable_refl {m : ℕ} {α : Type*} (h : m = m) : @castTable m m α h = id := by
  funext table
  rfl

theorem uniformRun_cast {m k : ℕ} (h : m = k) (input : BinaryGroupInputs.UniformInput m)
    (hC : input.Canonical) (hAd : BinaryGroupSamplers.UniformAdmissible input) (hm : m = 2 ∨ m = 3)
    (hC' : (BinaryTerminalGroupInputs.castUniform h input).Canonical)
    (hAd' : BinaryGroupSamplers.UniformAdmissible (BinaryTerminalGroupInputs.castUniform h input)) (hk : k = 2 ∨ k = 3)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    ((BinaryGroupPartialRun.uniformRun input hC hAd hm K N scalar bits pos hp).1.map (castTable h),
      (BinaryGroupPartialRun.uniformRun input hC hAd hm K N scalar bits pos hp).2) =
      BinaryGroupPartialRun.uniformRun (BinaryTerminalGroupInputs.castUniform h input) hC' hAd' hk K N scalar bits pos hp := by
  cases h
  simp only [castTable_refl, BinaryTerminalGroupInputs.castUniform, Option.map_id]
  rfl

theorem mixedRun_cast {m k : ℕ} (h : m = k) (input : BinaryGroupInputs.MixedInput m)
    (hC : input.Canonical) (hAd : BinaryGroupSamplers.MixedAdmissible input) (hm : m = 2 ∨ m = 3)
    (hC' : (BinaryTerminalGroupInputs.castMixed h input).Canonical)
    (hAd' : BinaryGroupSamplers.MixedAdmissible (BinaryTerminalGroupInputs.castMixed h input)) (hk : k = 2 ∨ k = 3)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    ((BinaryGroupPartialRun.mixedRun input hC hAd hm K N outer scalar bits pos hp).1.map
      (castTable (congrArg (fun size => size + 1) h)),
      (BinaryGroupPartialRun.mixedRun input hC hAd hm K N outer scalar bits pos hp).2) =
      BinaryGroupPartialRun.mixedRun (BinaryTerminalGroupInputs.castMixed h input) hC' hAd' hk K N outer scalar bits pos hp := by
  cases h
  simp only [castTable_refl, BinaryTerminalGroupInputs.castMixed, Option.map_id]
  rfl

theorem emit_cast {n m k : ℕ} (h : m = k) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) :
    BinaryGroupRoutes.emit (castRoutes h routes) (castTable h row) = BinaryGroupRoutes.emit routes row := by
  cases h
  rfl

theorem emitMixed_cast {n m k : ℕ} (h : m = k) (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (selected : Fin n) (row : FixedArrayTable (m + 1) SignedWord) :
    BinaryGroupRoutes.emitMixed (castRoutes h routes) selected (castTable (congrArg (fun size => size + 1) h) row) =
      BinaryGroupRoutes.emitMixed routes selected row := by
  cases h
  rfl

end Blotto.BinaryCachedTerminalPromises
