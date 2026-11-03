import Blotto.BinaryGroupInputs
import Blotto.BinaryFourSpecFixed

/-! The actual uniform and mixed small-group samplers retain original program
fallbacks and whole rows. Source validity is an erased existential certificate;
all descriptors and draws are made from stored words. -/

namespace Blotto.BinaryGroupSamplers
open BinaryRationalNormalization BinaryRationalEncoding BinaryGroupInputs

def UniformAdmissible {m : ℕ} (input : UniformInput m) : Prop := ∃ source : RationalUniformGroupSpec m, input.Refines source

def MixedAdmissible {m : ℕ} (input : MixedInput m) : Prop := ∃ source : RationalMixedGroupSpec m, input.Refines source

def uniformPrepared {m : ℕ} (input : UniformInput m) (hC : input.Canonical) (hAd : UniformAdmissible input) (hm : m=2 ∨ m=3) :
    BinaryStoredSegmentProgram.Prepared m 9 where
  table := uniformLottery input hm
  canonical := uniformLottery_canonical input hC hm
  nonnegative := by
    obtain ⟨source,hr⟩ := hAd
    intro slot
    rw [(uniformLottery_refines input source hC hr hm).1 slot]
    exact (source.lottery hm).nonnegative slot

def uniformSample {m : ℕ} (input : UniformInput m) (hC : input.Canonical) (hAd : UniformAdmissible input) (hm : m=2 ∨ m=3)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable m SignedWord :=
  (uniformPrepared input hC hAd hm).sample 0 K N scalar bits

theorem uniformSample_value {m : ℕ} (input : UniformInput m) (source : RationalUniformGroupSpec m) (hC : input.Canonical)
    (hr : input.Refines source) (hAd : UniformAdmissible input) (hm : m=2 ∨ m=3)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (g : Fin m) :
    value ((uniformSample input hC hAd hm K N scalar bits).read g) = (source.program hm K scalar).sample N bits g :=
  (uniformPrepared input hC hAd hm).sample_value (source.lottery hm) (uniformLottery_refines input source hC hr hm) 0 K N scalar bits g

theorem uniformSample_canonical {m : ℕ} (input : UniformInput m) (hC : input.Canonical) (hAd : UniformAdmissible input) (hm : m=2 ∨ m=3)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) : ∀ g, CanonicalWord ((uniformSample input hC hAd hm K N scalar bits).read g) :=
  (uniformPrepared input hC hAd hm).sample_canonical 0 K N scalar bits

def mixedTwoPrepared (input : MixedInput 2) (hC : input.Canonical) (hAd : MixedAdmissible input) :
    BinaryStoredSegmentProgram.Prepared 3 9 where
  table := BinaryThreeSpecCompiler.descriptor (mixedThree input)
  canonical := BinaryThreeSpecCompiler.descriptor_canonical _ (mixedThree_canonical input hC)
  nonnegative := by
    obtain ⟨source,hr⟩ := hAd
    intro slot
    rw [(BinaryThreeSpecCompiler.descriptor_refines _ source.threeInput (mixedThree_canonical input hC) (mixedThree_refines input source hr)).1 slot]
    exact source.threeInput.segmentLottery.nonnegative slot

theorem mixedFour_admissible (input : MixedInput 3) (_hC : input.Canonical) (hAd : MixedAdmissible input) :
    BinaryFourSpecSampler.Admissible (mixedFour input) := by
  obtain ⟨source,hr⟩ := hAd
  exact ⟨source.fourInput,mixedFour_refines input source hr⟩

def mixedSample {m : ℕ} (input : MixedInput m) (hC : input.Canonical) (hAd : MixedAdmissible input) (hm : m=2 ∨ m=3)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable (m+1) SignedWord := by
  by_cases h2 : m=2
  · subst m
    exact (mixedTwoPrepared input hC hAd).sample 0 K N scalar bits
  · have h3 : m=3 := hm.resolve_left h2
    subst m
    exact BinaryFourSpecFixed.sample (mixedFour input) (mixedFour_canonical input hC) (mixedFour_admissible input hC hAd) K N outer scalar bits

theorem mixedSample_value {m : ℕ} (input : MixedInput m) (source : RationalMixedGroupSpec m) (hC : input.Canonical)
    (hr : input.Refines source) (hAd : MixedAdmissible input) (hm : m=2 ∨ m=3)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (g : Fin (m+1)) :
    value ((mixedSample input hC hAd hm K N outer scalar bits).read g) = (source.program hm K outer scalar).sample N bits g := by
  rcases hm with rfl | rfl
  · exact (mixedTwoPrepared input hC hAd).sample_value source.threeInput.segmentLottery
      (BinaryThreeSpecCompiler.descriptor_refines _ _ (mixedThree_canonical input hC) (mixedThree_refines input source hr)) 0 K N scalar bits g
  · exact BinaryFourSpecFixed.sample_value _ _ (mixedFour_canonical input hC) (mixedFour_refines input source hr) (mixedFour_admissible input hC hAd) K N outer scalar bits g

theorem mixedSample_canonical {m : ℕ} (input : MixedInput m) (hC : input.Canonical) (hAd : MixedAdmissible input) (hm : m=2 ∨ m=3)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : ∀ g, CanonicalWord ((mixedSample input hC hAd hm K N outer scalar bits).read g) := by
  rcases hm with rfl | rfl
  · exact (mixedTwoPrepared input hC hAd).sample_canonical 0 K N scalar bits
  · exact BinaryFourSpecFixed.sample_canonical (mixedFour input) (mixedFour_canonical input hC) (mixedFour_admissible input hC hAd) K N outer scalar bits

theorem uniformSample_fullBudget {m : ℕ} (input : UniformInput m) (source : RationalUniformGroupSpec m) (hC : input.Canonical)
    (hr : input.Refines source) (hAd : UniformAdmissible input) (hm : m=2 ∨ m=3)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) :
    FullBudget (source.B : ℝ) (fun g => (value ((uniformSample input hC hAd hm K N scalar bits).read g) : ℝ)) := by
  have he : (fun g => (value ((uniformSample input hC hAd hm K N scalar bits).read g) : ℝ)) =
      fun g => ((source.program hm K scalar).sample N bits g : ℝ) := by
    funext g
    rw [uniformSample_value input source hC hr hAd hm]
  rw [he]
  exact (source.program hm K scalar).sample_fullBudget (source.program_leavesBudget hm K scalar) N bits

theorem mixedSample_fullBudget {m : ℕ} (input : MixedInput m) (source : RationalMixedGroupSpec m) (hC : input.Canonical)
    (hr : input.Refines source) (hAd : MixedAdmissible input) (hm : m=2 ∨ m=3)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    FullBudget (source.B : ℝ) (fun g => (value ((mixedSample input hC hAd hm K N outer scalar bits).read g) : ℝ)) := by
  have he : (fun g => (value ((mixedSample input hC hAd hm K N outer scalar bits).read g) : ℝ)) =
      fun g => ((source.program hm K outer scalar).sample N bits g : ℝ) := by
    funext g
    rw [mixedSample_value input source hC hr hAd hm]
  rw [he]
  exact (source.program hm K outer scalar).sample_fullBudget (source.program_leavesBudget hm K outer scalar) N bits

end Blotto.BinaryGroupSamplers
