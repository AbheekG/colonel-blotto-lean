import Blotto.BinaryPRGHeapFourWork
import Blotto.BinaryPRGWordControllerGroupWork

/-! The mixed-three group uses the physical reflected four-coordinate draw.
Other group regimes retain their measured implementations. -/

namespace Blotto.BinaryPRGHeapGroupWork
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryGroupInputs BinaryGroupSamplers BinaryCachedThreeDescriptorWork
open BinaryPRGWordControllerGroupWork (mixedTwoRun mixedTwoRun_erasure)

def mixedRun {m : ℕ} (store : Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    BinaryPRGWordControllerTerminal.Result store (m + 1) × ℕ := by
  by_cases h2 : m = 2
  · subst m
    exact mixedTwoRun store input hC hAd K scalar pc hp
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact BinaryPRGHeapFourWork.restoredRun store (mixedFour input) (mixedFour_canonical input hC)
      (mixedFour_admissible input hC hAd) K outer scalar pc hp

theorem mixedRun_erasure {m : ℕ} (store : Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hm : m = 2 ∨ m = 3) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedRun store input hC hAd hm K outer scalar pc hp).1 =
      BinaryPRGWordControllerTerminal.mixedRun store input hC hAd hm K outer scalar pc hp := by
  rcases hm with rfl | rfl
  · exact mixedTwoRun_erasure _ _ _ _ _ _ _ _
  · exact BinaryPRGHeapFourWork.restoredRun_erasure _ _ _ _ _ _ _ _ _

theorem mixedRun_cost_le {m : ℕ} (store : Store) (input : MixedInput m) (hC : input.Canonical)
    (hAd : MixedAdmissible input) (hm : m = 2 ∨ m = 3) (s : ℕ) (hs : 3 ≤ s)
    (hH : MixedHeights input s) (K : ℕ) (outer scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (mixedRun store input hC hAd hm K outer scalar pc hp).2 ≤
      (BinaryPRGWordControllerGroupWork.mixedRun store input hC hAd hm K outer scalar pc hp).2 +
        BinaryPRGHeapReflectedSetup.bound s store.width store.cap.value := by
  rcases hm with rfl | rfl
  · exact Nat.le_add_right _ _
  · obtain ⟨source,hr⟩ := hAd
    exact BinaryPRGHeapFourWork.restoredRun_cost_le store (mixedFour input) source.fourInput
      (mixedFour_canonical input hC) (mixedFour_refines input source hr)
      (mixedFour_admissible input hC ⟨source,hr⟩) s (by omega)
      (BinaryCachedFourParameterWork.source_four_heights input source hr s hH) K outer scalar pc hp

end Blotto.BinaryPRGHeapGroupWork
