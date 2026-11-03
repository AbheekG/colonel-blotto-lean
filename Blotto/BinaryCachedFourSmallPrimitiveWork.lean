import Blotto.BinarySmallRootPrimitiveRun
import Blotto.BinaryFourNativeOrderWork
import Blotto.BinaryCachedFourBranchWork

/-! Actual cached mixed-three original PRG inputs supply the small-root source
promise and every height in the measured branch. The native sorting/guard prices
also follow the cached fields. None is a caller-supplied width/source factory. -/

namespace Blotto.BinaryCachedFourSmallPrimitiveWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryGroupInputs
open BinaryCachedFourBranchWork BinaryCachedFourParameterWork BinaryCachedThreeDescriptorWork
open BinaryCachedTerminalPreparation BinaryCachedGroupInputHeight BinaryPRGResourceWork BinaryPRGTerminalWork

def smallRun (checked : Checked) (h : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (Option (FixedArrayTable 4 SignedWord) × ℕ) × BinarySmallRootPrimitiveRun.Ledger :=
  BinarySmallRootPrimitiveRun.run checked.ordered checked.ordered_canonical
    (BinaryFourAdmissibility.small_guard checked.ordered checked.ordered_canonical checked.ordered_admissible h)
    K N outer scalar bits

theorem smallRun_state (checked : Checked) (h : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (smallRun checked h K N outer scalar bits).1 = BinarySmallRootSample.run checked.ordered checked.ordered_canonical
      (BinaryFourAdmissibility.small_guard checked.ordered checked.ordered_canonical checked.ordered_admissible h) K N outer scalar bits :=
  BinarySmallRootPrimitiveRun.run_state _ _ _ K N outer scalar bits

theorem smallRun_bound (checked : Checked) (h : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (s : ℕ) (hs : 2 ≤ s) (hH : MixedHeights checked.input s)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (smallRun checked h K N outer scalar bits).2.recorded ≤ BinarySmallRootPrimitiveRun.bound s K N := by
  obtain ⟨source,hr⟩ := checked.admissible
  have hR := BinaryFourSpecSampler.orderedInput_refines (mixedFour checked.input) source.fourInput
    (mixedFour_canonical checked.input checked.canonical) (mixedFour_refines checked.input source hr)
  have hHeight := (source_four_heights checked.input source hr s hH).input
  have hCase := lt_of_not_ge (fun he => h ((BinaryFourParentCompiler.gluingCase_iff checked.ordered source.fourInput.input
    checked.ordered_canonical hR).mpr he))
  exact BinarySmallRootPrimitiveRun.run_bound _ source.fourInput.input checked.ordered_canonical hR _ hCase s hs hHeight K N outer scalar bits

theorem order_bound (checked : Checked) (s : ℕ) (hH : MixedHeights checked.input s) :
    (BinaryFourNativeOrderWork.orderedWithWork (mixedFour checked.input)).2 ≤ 3 * BinaryFactoryHeight.compareBound s :=
  BinaryFourNativeOrderWork.orderedWithWork_bound _ (mixedFour_canonical checked.input checked.canonical) s hH.2.1

theorem guard_bound (checked : Checked) (s : ℕ) (hH : MixedHeights checked.input s) :
    (BinaryFourNativeOrderWork.guardWithWork checked.ordered).2 ≤ BinaryFourNativeOrderWork.guardBound (max s 3) := by
  obtain ⟨source,hr⟩ := checked.admissible
  have hR := BinaryFourSpecSampler.orderedInput_refines (mixedFour checked.input) source.fourInput
    (mixedFour_canonical checked.input checked.canonical) (mixedFour_refines checked.input source hr)
  have hHeight := BinaryFourNativeOrderWork.input_height_of_refines checked.ordered source.fourInput.input hR s
    (source_four_heights checked.input source hr s hH).input
  have hm := le_max_left s 3
  exact BinaryFourNativeOrderWork.guardWithWork_bound _ checked.ordered_canonical _ (le_max_right _ _)
    ⟨hHeight.1.mono hm,hHeight.2.1.mono hm,hHeight.2.2.1.mono hm,hHeight.2.2.2.1.mono hm,
      hHeight.2.2.2.2.1.mono hm,hHeight.2.2.2.2.2.mono hm⟩

theorem cached_smallRun_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N → Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (hCount : (prepare (terminalInput request rich state)).count = 3) (selected : Fin n)
    (hPivot : (prepare (terminalInput request rich state)).pivot = some selected)
    (hSmall : ¬BinaryFourParentCompiler.gluingCase (cached request rich N bits state h hCount selected hPivot).ordered = true)
    (K M : ℕ) (outer scalar : Fin K → Bool) (choice : Fin M → Bool) :
    (smallRun (cached request rich N bits state h hCount selected hPivot) hSmall K M outer scalar choice).2.recorded ≤
      BinarySmallRootPrimitiveRun.bound (inputHeight request) K M :=
  smallRun_bound _ hSmall _ (inputHeight_two request) (cached_heights request rich N bits state h hCount selected hPivot)
    K M outer scalar choice

theorem cached_order_guard_bounds {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N → Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (hCount : (prepare (terminalInput request rich state)).count = 3) (selected : Fin n)
    (hPivot : (prepare (terminalInput request rich state)).pivot = some selected) :
    let checked := cached request rich N bits state h hCount selected hPivot
    (BinaryFourNativeOrderWork.orderedWithWork (mixedFour checked.input)).2 ≤ 3 * BinaryFactoryHeight.compareBound (inputHeight request) ∧
      (BinaryFourNativeOrderWork.guardWithWork checked.ordered).2 ≤ BinaryFourNativeOrderWork.guardBound (max (inputHeight request) 3) :=
  ⟨order_bound _ _ (cached_heights request rich N bits state h hCount selected hPivot),
    guard_bound _ _ (cached_heights request rich N bits state h hCount selected hPivot)⟩

end Blotto.BinaryCachedFourSmallPrimitiveWork
