import Blotto.BinaryCachedGroupInputHeight
import Blotto.BinaryThreeSpecWork
import Blotto.BinaryCachedTerminalPromises

/-! Uniform three-group and mixed two-group descriptors receive input heights
from the actual reached original PRG state. Source witnesses only transport
the checked compiler statements; no descriptor height or price oracle is a
runtime or theorem-input requirement. Mixed three-group/four-variable costs
remain a separate continuation obligation. -/

namespace Blotto.BinaryCachedThreeDescriptorWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryGroupInputs
open BinaryCachedTerminalPreparation BinaryCachedGroupInputHeight
open BinaryPRGResourceWork BinaryPRGTerminalWork

def UniformHeights {m : ℕ} (input : UniformInput m) (s : ℕ) : Prop :=
  RationalHeight (value input.budget) s ∧ ∀ g, RationalHeight (value (input.total.read g)) s

def MixedHeights {m : ℕ} (input : MixedInput m) (s : ℕ) : Prop :=
  RationalHeight (value input.budget) s ∧ (∀ g, RationalHeight (value (input.total.read g)) s) ∧
    RationalHeight (value input.ell) s ∧ RationalHeight (value input.probability) s

def ThreeHeights (input : BinaryThreeInputCompiler.Input) (s : ℕ) : Prop :=
  RationalHeight (value input.B) s ∧ RationalHeight (value input.a) s ∧ RationalHeight (value input.d) s ∧
    RationalHeight (value input.c) s ∧ RationalHeight (value input.p) s

def workBound (s : ℕ) : ℕ := BinaryThreeInputCompiler.workBound s + 1000 * (2 * s + 2) ^ 2 +
  108 * (4 * expressionHeightBudget s 4 + 3) + 220

theorem source_environment_heights (input : BinaryThreeInputCompiler.Input) (source : RationalThreeSpec)
    (hR : BinaryThreeSpecCompiler.Refines input source) (s : ℕ) (hH : ThreeHeights input s) :
    ∀ j, RationalHeight ((RationalThreeSpecCode.environment source).read j) s := by
  intro j
  fin_cases j
  · change RationalHeight source.B s
    rw [← hR.1]; exact hH.1
  · change RationalHeight source.a s
    rw [← hR.2.1]; exact hH.2.1
  · change RationalHeight source.d s
    rw [← hR.2.2.1]; exact hH.2.2.1
  · change RationalHeight source.c s
    rw [← hR.2.2.2.1]; exact hH.2.2.2.1
  · change RationalHeight source.p s
    rw [← hR.2.2.2.2]; exact hH.2.2.2.2

theorem uniform_heights_cast {m k : ℕ} (h : m = k) (input : UniformInput m) (s : ℕ) (hH : UniformHeights input s) :
    UniformHeights (BinaryTerminalGroupInputs.castUniform h input) s := by cases h; exact hH

theorem mixed_heights_cast {m k : ℕ} (h : m = k) (input : MixedInput m) (s : ℕ) (hH : MixedHeights input s) :
    MixedHeights (BinaryTerminalGroupInputs.castMixed h input) s := by cases h; exact hH

theorem uniformThree_heights (input : UniformInput 3) (s : ℕ) (hH : UniformHeights input s) (hs : 2 ≤ s) :
    ThreeHeights (uniformThree input) s :=
  ⟨hH.1, hH.2 0, hH.2 1, hH.2 2,
    by change RationalHeight (value BinaryExpressionCompiler.Constant.one.word) s
       rw [BinaryExpressionCompiler.Constant.word_value]; exact
      (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs⟩

theorem mixedThree_heights (input : MixedInput 2) (s : ℕ) (hH : MixedHeights input s) :
    ThreeHeights (mixedThree input) s :=
  ⟨hH.1, hH.2.1 0, hH.2.1 1, hH.2.2.1, hH.2.2.2⟩

theorem uniformThree_work (input : UniformInput 3) (hC : input.Canonical)
    (hAd : BinaryGroupSamplers.UniformAdmissible input) (s : ℕ) (hs : 2 ≤ s) (hH : UniformHeights input s) :
    BinaryThreeSpecCompiler.descriptorWork (uniformThree input) ≤ workBound s := by
  obtain ⟨source, hr⟩ := hAd
  exact BinaryThreeSpecCompiler.descriptorWork_bound (uniformThree input) source.threeInput
    (uniformThree_canonical input hC) (uniformThree_refines input source hr) s hs
    (source_environment_heights _ _ (uniformThree_refines input source hr) s (uniformThree_heights input s hH hs))

theorem mixedTwo_work (input : MixedInput 2) (hC : input.Canonical)
    (hAd : BinaryGroupSamplers.MixedAdmissible input) (s : ℕ) (hs : 2 ≤ s) (hH : MixedHeights input s) :
    BinaryThreeSpecCompiler.descriptorWork (mixedThree input) ≤ workBound s := by
  obtain ⟨source, hr⟩ := hAd
  exact BinaryThreeSpecCompiler.descriptorWork_bound (mixedThree input) source.threeInput
    (mixedThree_canonical input hC) (mixedThree_refines input source hr) s hs
    (source_environment_heights _ _ (mixedThree_refines input source hr) s (mixedThree_heights input s hH))

theorem cached_uniform_heights {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state) :
    UniformHeights (prepare (terminalInput request rich state)).uniform (inputHeight request) :=
  ⟨budget_height request rich, cached_total_height request rich N bits state h⟩

theorem cached_mixed_heights {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state) (selected : Fin n)
    (hPivot : (prepare (terminalInput request rich state)).pivot = some selected) :
    MixedHeights (prepare (terminalInput request rich state)).mixed (inputHeight request) :=
  ⟨budget_height request rich, cached_total_height request rich N bits state h,
    cached_pivot_heights request rich N bits state h selected hPivot⟩

theorem uniform_canonical_forward {m k : ℕ} (h : m = k) (input : UniformInput m) (hC : input.Canonical) :
    (BinaryTerminalGroupInputs.castUniform h input).Canonical := by cases h; exact hC

theorem uniform_admissible_forward {m k : ℕ} (h : m = k) (input : UniformInput m)
    (hAd : BinaryGroupSamplers.UniformAdmissible input) :
    BinaryGroupSamplers.UniformAdmissible (BinaryTerminalGroupInputs.castUniform h input) := by cases h; exact hAd

theorem mixed_canonical_forward {m k : ℕ} (h : m = k) (input : MixedInput m) (hC : input.Canonical) :
    (BinaryTerminalGroupInputs.castMixed h input).Canonical := by cases h; exact hC

theorem mixed_admissible_forward {m k : ℕ} (h : m = k) (input : MixedInput m)
    (hAd : BinaryGroupSamplers.MixedAdmissible input) :
    BinaryGroupSamplers.MixedAdmissible (BinaryTerminalGroupInputs.castMixed h input) := by cases h; exact hAd

theorem cached_uniform_three_work {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (hCount : (prepare (terminalInput request rich state)).count = 3)
    (hPivot : (prepare (terminalInput request rich state)).pivot = none) :
    BinaryThreeSpecCompiler.descriptorWork (uniformThree
      (BinaryTerminalGroupInputs.castUniform hCount (prepare (terminalInput request rich state)).uniform)) ≤
        workBound (inputHeight request) := by
  let cached := prepare (terminalInput request rich state)
  have hC := terminal_canonical request rich state
  have hAd := terminal_admissible request rich N bits state h
  exact uniformThree_work _ (uniform_canonical_forward hCount cached.uniform (cached.uniform_canonical hC))
    (uniform_admissible_forward hCount cached.uniform
      (BinaryCachedTerminalPromises.Prepared.uniform_admissible cached hC hAd hPivot))
    _ (inputHeight_two request) (uniform_heights_cast hCount _ _ (cached_uniform_heights request rich N bits state h))

theorem cached_mixed_two_work {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (hCount : (prepare (terminalInput request rich state)).count = 2) (selected : Fin n)
    (hPivot : (prepare (terminalInput request rich state)).pivot = some selected) :
    BinaryThreeSpecCompiler.descriptorWork (mixedThree
      (BinaryTerminalGroupInputs.castMixed hCount (prepare (terminalInput request rich state)).mixed)) ≤
        workBound (inputHeight request) := by
  let cached := prepare (terminalInput request rich state)
  have hC := terminal_canonical request rich state
  have hAd := terminal_admissible request rich N bits state h
  exact mixedTwo_work _ (mixed_canonical_forward hCount cached.mixed (cached.mixed_canonical hC selected hPivot))
    (mixed_admissible_forward hCount cached.mixed
      (BinaryCachedTerminalPromises.Prepared.mixed_admissible cached hC hAd selected hPivot))
    _ (inputHeight_two request) (mixed_heights_cast hCount _ _ (cached_mixed_heights request rich N bits state h selected hPivot))

end Blotto.BinaryCachedThreeDescriptorWork
