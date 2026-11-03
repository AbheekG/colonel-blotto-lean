import Blotto.BinaryStoredSegmentDrawWork
import Blotto.BinaryCachedThreePointWork

/-! Primitive work for actual uniform-three and mixed-two indexed draws now
includes categorical preparation/residual coins and selected interpolation.
Both descriptor weight and endpoint heights come from the original request's
reached cached state. Exhaustion and the one absolute reader cap are retained.
Reflected four-variable continuations and complete compiled costs are separate. -/

namespace Blotto.BinaryCachedThreeSelectionWork
open BinaryRationalNormalization BinaryGroupInputs BinaryCachedThreeDescriptorWork
open BinaryCachedTerminalPreparation BinaryCachedGroupInputHeight
open BinaryPRGResourceWork BinaryPRGTerminalWork

def drawBound (s K remaining : ℕ) : ℕ :=
  BinaryStoredSegmentChoiceWork.selectionBound 9 (expressionHeightBudget s 18) remaining +
    BinaryStoredSegmentDrawWork.pointBound 3 (expressionHeightBudget s 4) K

theorem descriptor_draw_work (prepared : BinaryStoredSegmentProgram.Prepared 3 9)
    (input : BinaryThreeInputCompiler.Input) (source : RationalThreeSpec)
    (hC : input.Canonical) (hR : BinaryThreeSpecCompiler.Refines input source)
    (hTable : prepared.table = BinaryThreeSpecCompiler.descriptor input)
    (s : ℕ) (hs : 2 ≤ s) (hH : ThreeHeights input s)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (BinaryStoredSegmentDrawWork.runIndexedWork prepared 0 K N scalar bits pos hp).2 ≤ drawBound s K (N - pos) := by
  have hEnv := source_environment_heights input source hR s hH
  have hr : prepared.table.Refines source.segmentLottery := hTable.symm ▸ BinaryThreeSpecCompiler.descriptor_refines input source hC hR
  exact BinaryStoredSegmentDrawWork.runIndexedWork_bound prepared source.segmentLottery hr
    (expressionHeightBudget s 18) (expressionHeightBudget s 4) (hs.trans (expressionHeightBudget_ge_input s 4))
    (fun slot => RationalThreeSpecCode.weight_height source slot s hs hEnv)
    (fun slot j => RationalThreeSpecCode.endpoint_heights source slot j s hs hEnv) 0 K N scalar bits pos hp

theorem uniformThree_draw_work (input : UniformInput 3) (hC : input.Canonical)
    (hAd : BinaryGroupSamplers.UniformAdmissible input) (s : ℕ) (hs : 2 ≤ s) (hH : UniformHeights input s)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (BinaryStoredSegmentDrawWork.runIndexedWork (BinaryGroupSamplers.uniformPrepared input hC hAd (.inr rfl))
      0 K N scalar bits pos hp).2 ≤ drawBound s K (N - pos) := by
  obtain ⟨source, hr⟩ := hAd
  exact descriptor_draw_work _ (uniformThree input) source.threeInput
    (uniformThree_canonical input hC) (uniformThree_refines input source hr) rfl s hs
    (uniformThree_heights input s hH hs) K N scalar bits pos hp

theorem mixedTwo_draw_work (input : MixedInput 2) (hC : input.Canonical)
    (hAd : BinaryGroupSamplers.MixedAdmissible input) (s : ℕ) (hs : 2 ≤ s) (hH : MixedHeights input s)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (BinaryStoredSegmentDrawWork.runIndexedWork (BinaryGroupSamplers.mixedTwoPrepared input hC hAd)
      0 K N scalar bits pos hp).2 ≤ drawBound s K (N - pos) := by
  obtain ⟨source, hr⟩ := hAd
  exact descriptor_draw_work _ (mixedThree input) source.threeInput
    (mixedThree_canonical input hC) (mixedThree_refines input source hr) rfl s hs
    (mixedThree_heights input s hH) K N scalar bits pos hp

theorem cached_uniform_three_draw_work {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (hCount : (prepare (terminalInput request rich state)).count = 3)
    (hPivot : (prepare (terminalInput request rich state)).pivot = none)
    (K : ℕ) (scalar : Fin K → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (BinaryStoredSegmentDrawWork.runIndexedWork
      (BinaryGroupSamplers.uniformPrepared
        (BinaryTerminalGroupInputs.castUniform hCount (prepare (terminalInput request rich state)).uniform)
        (uniform_canonical_forward hCount _ ((prepare (terminalInput request rich state)).uniform_canonical
          (terminal_canonical request rich state)))
        (uniform_admissible_forward hCount _ (BinaryCachedTerminalPromises.Prepared.uniform_admissible
          (prepare (terminalInput request rich state)) (terminal_canonical request rich state)
          (terminal_admissible request rich N bits state h) hPivot)) (.inr rfl))
      0 K N scalar bits pos hp).2 ≤ drawBound (inputHeight request) K (N - pos) := by
  exact uniformThree_draw_work _ _ _ _ (inputHeight_two request)
    (uniform_heights_cast hCount _ _ (cached_uniform_heights request rich N bits state h)) K N scalar bits pos hp

theorem cached_mixed_two_draw_work {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (hCount : (prepare (terminalInput request rich state)).count = 2) (selected : Fin n)
    (hPivot : (prepare (terminalInput request rich state)).pivot = some selected)
    (K : ℕ) (scalar : Fin K → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (BinaryStoredSegmentDrawWork.runIndexedWork
      (BinaryGroupSamplers.mixedTwoPrepared
        (BinaryTerminalGroupInputs.castMixed hCount (prepare (terminalInput request rich state)).mixed)
        (mixed_canonical_forward hCount _ ((prepare (terminalInput request rich state)).mixed_canonical
          (terminal_canonical request rich state) selected hPivot))
        (mixed_admissible_forward hCount _ (BinaryCachedTerminalPromises.Prepared.mixed_admissible
          (prepare (terminalInput request rich state)) (terminal_canonical request rich state)
          (terminal_admissible request rich N bits state h) selected hPivot)))
      0 K N scalar bits pos hp).2 ≤ drawBound (inputHeight request) K (N - pos) := by
  exact mixedTwo_draw_work _ _ _ _ (inputHeight_two request)
    (mixed_heights_cast hCount _ _ (cached_mixed_heights request rich N bits state h selected hPivot)) K N scalar bits pos hp

end Blotto.BinaryCachedThreeSelectionWork
