import Blotto.BinaryGroupRetainedPrimitiveRun
import Blotto.BinaryCachedTerminalRun

/-! Cached terminal draws use actual priced native group continuations in all
four group/pivot cases. One retained packing/totals/routes/pivot preparation is
consumed. Exact output/none/absolute-position semantics and original-request
field-derived primitive prices hold; route emission and model costs are separate. -/

namespace Blotto.BinaryCachedTerminalPrimitiveRun
open BinaryRationalNormalization BinaryRationalEncoding BinaryCachedTerminalPreparation BinaryCachedTerminalPromises
open BinaryCachedThreeDescriptorWork BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedGroupInputHeight

def runPrepared {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (Option (FixedArrayTable n SignedWord) × ℕ) × ℕ :=
  match hs : prepared.pivot with
  | none =>
      let drawn := BinaryGroupRetainedPrimitiveRun.uniformRun prepared.uniform (prepared.uniform_canonical hC)
        (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hs)
        (prepared.count_bound hC hAd) K N scalar bits pos hp
      ((drawn.1.1.map (BinaryGroupRoutes.emit prepared.routes),drawn.1.2),drawn.2)
  | some selected =>
      let drawn := BinaryGroupRetainedPrimitiveRun.mixedRun prepared.mixed (prepared.mixed_canonical hC selected hs)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hs)
        (prepared.count_bound hC hAd) K N outer scalar bits pos hp
      ((drawn.1.1.map (BinaryGroupRoutes.emitMixed prepared.routes selected),drawn.1.2),drawn.2)

theorem runPrepared_state {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (runPrepared prepared hC hAd K N outer scalar bits pos hp).1 =
      BinaryCachedTerminalRun.runPrepared prepared hC hAd K N outer scalar bits pos hp := by
  unfold runPrepared BinaryCachedTerminalRun.runPrepared
  dsimp only
  split
  · rename_i hNone
    rw [BinaryGroupRetainedPrimitiveRun.uniformRun_state]
    split
    · rfl
    · rename_i selected hSome
      cases hNone.symm.trans hSome
  · rename_i selected hSome
    rw [BinaryGroupRetainedPrimitiveRun.mixedRun_state]
    split
    · rename_i hNone
      cases hSome.symm.trans hNone
    · rename_i other hOther
      have he : selected = other := Option.some.inj (hSome.symm.trans hOther)
      subst other
      rfl

def bound (s K remaining : ℕ) : ℕ := BinaryGroupRetainedPrimitiveRun.descriptorDrawBound 3 s K remaining +
  BinaryGroupRetainedPrimitiveRun.mixedBound s K remaining

theorem descriptorDrawBound_mono_dimension {m k : ℕ} (h : m ≤ k) (s K remaining : ℕ) :
    BinaryGroupRetainedPrimitiveRun.descriptorDrawBound m s K remaining ≤
      BinaryGroupRetainedPrimitiveRun.descriptorDrawBound k s K remaining := by
  unfold BinaryGroupRetainedPrimitiveRun.descriptorDrawBound BinaryStoredSegmentDrawWork.pointBound
  gcongr

theorem runPrepared_bound {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hU : UniformHeights prepared.uniform s)
    (hM : ∀ selected, prepared.pivot = some selected → MixedHeights prepared.mixed s)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (runPrepared prepared hC hAd K N outer scalar bits pos hp).2 ≤ bound s K (N - pos) := by
  have hm := prepared.count_bound hC hAd
  have hm3 : prepared.count ≤ 3 := by rcases hm with h | h <;> omega
  unfold runPrepared
  dsimp only
  split
  · rename_i hNone
    have hd := BinaryGroupRetainedPrimitiveRun.uniformRun_bound prepared.uniform (prepared.uniform_canonical hC)
      (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hNone) hm s hs hU K N scalar bits pos hp
    exact (hd.trans (descriptorDrawBound_mono_dimension hm3 s K (N - pos))).trans (Nat.le_add_right _ _)
  · rename_i selected hSome
    have hd := BinaryGroupRetainedPrimitiveRun.mixedRun_bound prepared.mixed (prepared.mixed_canonical hC selected hSome)
      (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hSome) hm s hs (hM selected hSome) K N outer scalar bits pos hp
    exact hd.trans (Nat.le_add_left _ _)

noncomputable def requestHeight {n : ℕ} (request : BinaryPRGRequest.Request n) : ℕ := max (inputHeight request) 3

theorem uniformHeights_mono {m s t : ℕ} {input : BinaryGroupInputs.UniformInput m}
    (h : UniformHeights input s) (hst : s ≤ t) : UniformHeights input t := ⟨h.1.mono hst,fun j => (h.2 j).mono hst⟩

theorem mixedHeights_mono {m s t : ℕ} {input : BinaryGroupInputs.MixedInput m}
    (h : MixedHeights input s) (hst : s ≤ t) : MixedHeights input t :=
  ⟨h.1.mono hst,fun j => (h.2.1 j).mono hst,h.2.2.1.mono hst,h.2.2.2.mono hst⟩

theorem reached_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N → Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (K M : ℕ) (outer scalar : Fin K → Bool) (choice : Fin M → Bool) (pos : ℕ) (hp : pos ≤ M) :
    (runPrepared (prepare (terminalInput request rich state)) (terminal_canonical request rich state)
      (terminal_admissible request rich N bits state h) K M outer scalar choice pos hp).2 ≤ bound (requestHeight request) K (M - pos) :=
  runPrepared_bound _ _ _ _ (le_max_right _ _)
    (uniformHeights_mono (cached_uniform_heights request rich N bits state h) (le_max_left _ _))
    (fun selected hPivot => mixedHeights_mono (cached_mixed_heights request rich N bits state h selected hPivot) (le_max_left _ _))
    K M outer scalar choice pos hp

end Blotto.BinaryCachedTerminalPrimitiveRun
