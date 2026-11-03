import Blotto.BinaryCachedThreeDescriptorWork

/-! Actual three-variable midpoint/interpolation work is priced from cached
original PRG input heights. Bounds cover every descriptor slot, so they hold
after any native categorical choice. Categorical and four-variable reflected
continuation prices remain distinct obligations. -/

namespace Blotto.BinaryCachedThreePointWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryGroupInputs
open BinaryCachedTerminalPreparation BinaryCachedGroupInputHeight BinaryCachedThreeDescriptorWork
open BinaryPRGResourceWork BinaryPRGTerminalWork

def pointBound (s K : ℕ) : ℕ := 180 * (K + 3) ^ 3 +
  27 * BinaryRationalExpression.uniformPrice (expressionHeightBudget (max (expressionHeightBudget s 4) (K + 2)) 3) +
    6 * (3 + 4 * expressionHeightBudget (max (expressionHeightBudget s 4) (K + 2)) 3) + 7

theorem descriptor_point_work (input : BinaryThreeInputCompiler.Input) (source : RationalThreeSpec)
    (hC : input.Canonical) (hR : BinaryThreeSpecCompiler.Refines input source)
    (s : ℕ) (hs : 2 ≤ s) (hH : ThreeHeights input s) (slot : Fin 9) (K : ℕ) (scalar : Fin K → Bool) :
    BinarySegmentPoint.sampleWork (BinaryThreeSpecCompiler.descriptor input) slot K scalar ≤ pointBound s K := by
  have hEnv := source_environment_heights input source hR s hH
  have hEndpoints := fun slot j => RationalThreeSpecCode.endpoint_heights source slot j s hs hEnv
  exact BinarySegmentPoint.sampleWork_bound (BinaryThreeSpecCompiler.descriptor input) source.segmentLottery
    (BinaryThreeSpecCompiler.descriptor_canonical input hC) (BinaryThreeSpecCompiler.descriptor_refines input source hC hR)
    (expressionHeightBudget s 4) (hs.trans (expressionHeightBudget_ge_input s 4)) hEndpoints slot K scalar

theorem uniformThree_point_work (input : UniformInput 3) (hC : input.Canonical)
    (hAd : BinaryGroupSamplers.UniformAdmissible input) (s : ℕ) (hs : 2 ≤ s) (hH : UniformHeights input s)
    (slot : Fin 9) (K : ℕ) (scalar : Fin K → Bool) :
    BinarySegmentPoint.sampleWork (BinaryThreeSpecCompiler.descriptor (uniformThree input)) slot K scalar ≤ pointBound s K := by
  obtain ⟨source, hr⟩ := hAd
  exact descriptor_point_work _ source.threeInput (uniformThree_canonical input hC) (uniformThree_refines input source hr)
    s hs (uniformThree_heights input s hH hs) slot K scalar

theorem mixedTwo_point_work (input : MixedInput 2) (hC : input.Canonical)
    (hAd : BinaryGroupSamplers.MixedAdmissible input) (s : ℕ) (hs : 2 ≤ s) (hH : MixedHeights input s)
    (slot : Fin 9) (K : ℕ) (scalar : Fin K → Bool) :
    BinarySegmentPoint.sampleWork (BinaryThreeSpecCompiler.descriptor (mixedThree input)) slot K scalar ≤ pointBound s K := by
  obtain ⟨source, hr⟩ := hAd
  exact descriptor_point_work _ source.threeInput (mixedThree_canonical input hC) (mixedThree_refines input source hr)
    s hs (mixedThree_heights input s hH) slot K scalar

theorem cached_uniform_three_point_work {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (hCount : (prepare (terminalInput request rich state)).count = 3)
    (hPivot : (prepare (terminalInput request rich state)).pivot = none)
    (slot : Fin 9) (K : ℕ) (scalar : Fin K → Bool) :
    BinarySegmentPoint.sampleWork (BinaryThreeSpecCompiler.descriptor (uniformThree
      (BinaryTerminalGroupInputs.castUniform hCount (prepare (terminalInput request rich state)).uniform))) slot K scalar ≤
        pointBound (inputHeight request) K := by
  let cached := prepare (terminalInput request rich state)
  have hC := terminal_canonical request rich state
  have hAd := terminal_admissible request rich N bits state h
  exact uniformThree_point_work _ (uniform_canonical_forward hCount cached.uniform (cached.uniform_canonical hC))
    (uniform_admissible_forward hCount cached.uniform
      (BinaryCachedTerminalPromises.Prepared.uniform_admissible cached hC hAd hPivot))
    _ (inputHeight_two request) (uniform_heights_cast hCount _ _ (cached_uniform_heights request rich N bits state h)) slot K scalar

theorem cached_mixed_two_point_work {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (hCount : (prepare (terminalInput request rich state)).count = 2) (selected : Fin n)
    (hPivot : (prepare (terminalInput request rich state)).pivot = some selected)
    (slot : Fin 9) (K : ℕ) (scalar : Fin K → Bool) :
    BinarySegmentPoint.sampleWork (BinaryThreeSpecCompiler.descriptor (mixedThree
      (BinaryTerminalGroupInputs.castMixed hCount (prepare (terminalInput request rich state)).mixed))) slot K scalar ≤
        pointBound (inputHeight request) K := by
  let cached := prepare (terminalInput request rich state)
  have hC := terminal_canonical request rich state
  have hAd := terminal_admissible request rich N bits state h
  exact mixedTwo_point_work _ (mixed_canonical_forward hCount cached.mixed (cached.mixed_canonical hC selected hPivot))
    (mixed_admissible_forward hCount cached.mixed
      (BinaryCachedTerminalPromises.Prepared.mixed_admissible cached hC hAd selected hPivot))
    _ (inputHeight_two request) (mixed_heights_cast hCount _ _ (cached_mixed_heights request rich N bits state h selected hPivot)) slot K scalar

end Blotto.BinaryCachedThreePointWork
