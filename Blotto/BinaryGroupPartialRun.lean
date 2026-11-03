import Blotto.BinaryGroupSamplers
import Blotto.BinaryFourSpecPartialRun
import Blotto.BinaryTerminalGroupInputs

/-! Partial native small-group execution preserves none and reader position;
no small fallback is substituted for an outer PRG exhaustion result. -/

namespace Blotto.BinaryGroupPartialRun
open BinaryRationalNormalization BinaryRationalEncoding BinaryGroupInputs BinaryGroupSamplers

noncomputable def sourceRow {n : ℕ} (row : FixedArrayTable n SignedWord) : Fin n → ℚ := fun j => value (row.read j)

def uniformRun {m : ℕ} (input : UniformInput m) (hC : input.Canonical) (hAd : UniformAdmissible input) (hm : m=2 ∨ m=3)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) : Option (FixedArrayTable m SignedWord) × ℕ :=
  (uniformPrepared input hC hAd hm).runIndexed 0 K N scalar bits pos hp

theorem uniformRun_refines {m : ℕ} (input : UniformInput m) (source : RationalUniformGroupSpec m) (hC : input.Canonical)
    (hr : input.Refines source) (hAd : UniformAdmissible input) (hm : m=2 ∨ m=3)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    ((uniformRun input hC hAd hm K N scalar bits pos hp).1.map sourceRow,(uniformRun input hC hAd hm K N scalar bits pos hp).2) =
      (source.program hm K scalar).machine.runCursorIndexed N bits (.state (source.program hm K scalar).start) pos hp :=
  (uniformPrepared input hC hAd hm).runIndexed_refines (source.lottery hm) (uniformLottery_refines input source hC hr hm) 0 K N scalar bits pos hp

def mixedRun {m : ℕ} (input : MixedInput m) (hC : input.Canonical) (hAd : MixedAdmissible input) (hm : m=2 ∨ m=3)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) : Option (FixedArrayTable (m+1) SignedWord) × ℕ := by
  by_cases h2 : m=2
  · subst m
    exact (mixedTwoPrepared input hC hAd).runIndexed 0 K N scalar bits pos hp
  · have h3 : m=3 := hm.resolve_left h2
    subst m
    exact BinaryFourSpecPartialRun.runIndexed (mixedFour input) (mixedFour_canonical input hC)
      (mixedFour_admissible input hC hAd) K N outer scalar bits pos hp

theorem mixedRun_refines {m : ℕ} (input : MixedInput m) (source : RationalMixedGroupSpec m) (hC : input.Canonical)
    (hr : input.Refines source) (hAd : MixedAdmissible input) (hm : m=2 ∨ m=3)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    ((mixedRun input hC hAd hm K N outer scalar bits pos hp).1.map sourceRow,(mixedRun input hC hAd hm K N outer scalar bits pos hp).2) =
      (source.program hm K outer scalar).machine.runCursorIndexed N bits (.state (source.program hm K outer scalar).start) pos hp := by
  rcases hm with rfl | rfl
  · exact (mixedTwoPrepared input hC hAd).runIndexed_refines source.threeInput.segmentLottery
      (BinaryThreeSpecCompiler.descriptor_refines _ _ (mixedThree_canonical input hC) (mixedThree_refines input source hr)) 0 K N scalar bits pos hp
  · exact BinaryFourSpecPartialRun.runIndexed_refines (mixedFour input) source.fourInput (mixedFour_canonical input hC)
      (mixedFour_refines input source hr) (mixedFour_admissible input hC hAd) K N outer scalar bits pos hp

def transportRow {m k : ℕ} (he : m=k) (row : Fin k → ℚ) : Fin m → ℚ := fun g => row (g.cast he)

theorem transportRow_refl {m : ℕ} (he : m=m) : @transportRow m m he = id := by
  funext row g
  rfl

theorem uniformRun_transport {m k : ℕ} (he : m=k) (input : UniformInput k) (source : RationalUniformGroupSpec m)
    (hC : input.Canonical) (hr : (BinaryTerminalGroupInputs.castUniform he.symm input).Refines source)
    (hAd : UniformAdmissible input) (hm : m=2 ∨ m=3) (hk : k=2 ∨ k=3)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    WordMappedIndexedRefinement.mapResult (transportRow he)
      ((uniformRun input hC hAd hk K N scalar bits pos hp).1.map sourceRow,(uniformRun input hC hAd hk K N scalar bits pos hp).2) =
      (source.program hm K scalar).machine.runCursorIndexed N bits (.state (source.program hm K scalar).start) pos hp := by
  cases he
  simp only [WordMappedIndexedRefinement.mapResult,transportRow_refl,Option.map_id]
  exact uniformRun_refines input source hC hr hAd hm K N scalar bits pos hp

theorem mixedRun_transport {m k : ℕ} (he : m=k) (input : MixedInput k) (source : RationalMixedGroupSpec m)
    (hC : input.Canonical) (hr : (BinaryTerminalGroupInputs.castMixed he.symm input).Refines source)
    (hAd : MixedAdmissible input) (hm : m=2 ∨ m=3) (hk : k=2 ∨ k=3)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    WordMappedIndexedRefinement.mapResult (transportRow (congrArg (fun size => size+1) he))
      ((mixedRun input hC hAd hk K N outer scalar bits pos hp).1.map sourceRow,(mixedRun input hC hAd hk K N outer scalar bits pos hp).2) =
      (source.program hm K outer scalar).machine.runCursorIndexed N bits (.state (source.program hm K outer scalar).start) pos hp := by
  cases he
  simp only [WordMappedIndexedRefinement.mapResult,transportRow_refl,Option.map_id]
  exact mixedRun_refines input source hC hr hAd hm K N outer scalar bits pos hp

theorem uniformRun_canonical {m : ℕ} (input : UniformInput m) (hC : input.Canonical) (hAd : UniformAdmissible input) (hm : m=2 ∨ m=3)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) (row : FixedArrayTable m SignedWord)
    (hs : (uniformRun input hC hAd hm K N scalar bits pos hp).1=some row) : ∀ g, CanonicalWord (row.read g) := by
  obtain ⟨slot,hSlot,rfl⟩ := Option.map_eq_some_iff.mp hs
  exact BinarySegmentPoint.sample_canonical _ slot K scalar (uniformPrepared input hC hAd hm).canonical

theorem mixedRun_canonical {m : ℕ} (input : MixedInput m) (hC : input.Canonical) (hAd : MixedAdmissible input) (hm : m=2 ∨ m=3)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) (row : FixedArrayTable (m+1) SignedWord)
    (hs : (mixedRun input hC hAd hm K N outer scalar bits pos hp).1=some row) : ∀ g, CanonicalWord (row.read g) := by
  rcases hm with rfl | rfl
  · obtain ⟨slot,hSlot,rfl⟩ := Option.map_eq_some_iff.mp hs
    exact BinarySegmentPoint.sample_canonical _ slot K scalar (mixedTwoPrepared input hC hAd).canonical
  · exact BinaryFourSpecPartialRun.runIndexed_canonical _ (mixedFour_canonical input hC) (mixedFour_admissible input hC hAd)
      K N outer scalar bits pos hp row hs

end Blotto.BinaryGroupPartialRun
