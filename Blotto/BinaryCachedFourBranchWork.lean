import Blotto.BinaryGluingDrawWork
import Blotto.BinarySmallUniformDrawWork
import Blotto.BinaryReflectedSetupWork

/-! Actual cached mixed-three inputs supply canonical/admissible ordered
six-word data and all source heights. Primitive prices join guarded gluing
fixed draws, small uniform indexed draws and reflected setup/capacity production.
The reflected resource/conditional terminal loop and complete model remain open. -/

namespace Blotto.BinaryCachedFourBranchWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryGroupInputs
open BinaryCachedThreeDescriptorWork BinaryCachedFourParameterWork
open BinaryCachedTerminalPreparation BinaryCachedGroupInputHeight
open BinaryPRGResourceWork BinaryPRGTerminalWork

structure Checked where
  input : MixedInput 3
  canonical : input.Canonical
  admissible : BinaryGroupSamplers.MixedAdmissible input

def Checked.ordered (checked : Checked) : BinaryFourParameters.Input :=
  BinaryFourSpecSampler.orderedInput (mixedFour checked.input)

theorem Checked.ordered_canonical (checked : Checked) : checked.ordered.Canonical :=
  BinaryFourSpecSampler.orderedInput_canonical _ (mixedFour_canonical checked.input checked.canonical)

theorem Checked.ordered_admissible (checked : Checked) : BinaryFourAdmissibility.Admissible checked.ordered :=
  BinaryFourSpecSampler.orderedInput_admissible _ (mixedFour_canonical checked.input checked.canonical)
    (BinaryGroupSamplers.mixedFour_admissible checked.input checked.canonical checked.admissible)

def Checked.gluing (checked : Checked) (h : BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable 4 SignedWord × ℕ :=
  BinaryGluingDrawWork.fixedSampleWithWork checked.ordered checked.ordered_canonical
    (BinaryFourAdmissibility.gluing_guard checked.ordered checked.ordered_canonical checked.ordered_admissible h) K N scalar bits

def Checked.gluingIndexed (checked : Checked) (h : BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (Option (FixedArrayTable 4 SignedWord) × ℕ) × ℕ :=
  BinaryGluingDrawWork.partialWithWork checked.ordered checked.ordered_canonical
    (BinaryFourAdmissibility.gluing_guard checked.ordered checked.ordered_canonical checked.ordered_admissible h)
    K N scalar bits pos hp

def Checked.smallUniform (checked : Checked) (h : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (Option (FixedArrayTable 4 SignedWord) × ℕ) × ℕ :=
  BinarySmallUniformDrawWork.runIndexedWithWork checked.ordered checked.ordered_canonical
    (BinaryFourAdmissibility.small_guard checked.ordered checked.ordered_canonical checked.ordered_admissible h)
    K N scalar bits pos hp

theorem Checked.bounds (checked : Checked) (s : ℕ) (hs : 2 ≤ s) (hH : MixedHeights checked.input s)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (BinaryReflectedSetupWork.prepareWithWork checked.ordered).2 ≤ BinaryReflectedSetupWork.bound s ∧
    (∀ h : BinaryFourParentCompiler.gluingCase checked.ordered = true,
      (checked.gluing h K N scalar bits).2 ≤ BinaryGluingDrawWork.bound s K N ∧
      (checked.gluingIndexed h K N scalar bits pos hp).2 ≤ BinaryGluingDrawWork.partialBound s K (N - pos)) ∧
    (∀ h : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true,
      (checked.smallUniform h K N scalar bits pos hp).2 ≤ BinarySmallUniformDrawWork.bound s K (N - pos) ∧
      (BinaryReflectedSetupWork.capacityWithWork (BinaryReflectedFourSetup.prepare checked.ordered)).2 ≤
        3 * (12000 * (2 + 2 * expressionHeightBudget s 14) ^ 3)) := by
  obtain ⟨source, hr⟩ := checked.admissible
  have hR := BinaryFourSpecSampler.orderedInput_refines (mixedFour checked.input) source.fourInput
    (mixedFour_canonical checked.input checked.canonical) (mixedFour_refines checked.input source hr)
  have hHeight := (source_four_heights checked.input source hr s hH).input
  refine ⟨BinaryReflectedSetupWork.prepareWithWork_bound checked.ordered source.fourInput.input
    checked.ordered_canonical hR s hs hHeight, ?_, ?_⟩
  · intro h
    have hCase := (BinaryFourParentCompiler.gluingCase_iff checked.ordered source.fourInput.input checked.ordered_canonical hR).mp h
    exact ⟨BinaryGluingDrawWork.fixedSampleWithWork_bound checked.ordered source.fourInput.input checked.ordered_canonical hR
      _ hCase s hs hHeight K N scalar bits,
      BinaryGluingDrawWork.partialWithWork_bound checked.ordered source.fourInput.input checked.ordered_canonical hR
        _ hCase s hs hHeight K N scalar bits pos hp⟩
  · intro h
    have hCase := lt_of_not_ge (fun he => h ((BinaryFourParentCompiler.gluingCase_iff checked.ordered source.fourInput.input
      checked.ordered_canonical hR).mpr he))
    exact ⟨BinarySmallUniformDrawWork.runIndexedWithWork_bound checked.ordered source.fourInput.input checked.ordered_canonical hR
      _ hCase s hs hHeight K N scalar bits pos hp,
      BinaryReflectedSetupWork.actual_capacityWithWork_bound checked.ordered source.fourInput.input checked.ordered_canonical hR
        hCase s hs hHeight⟩

def cached {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N → Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (hCount : (prepare (terminalInput request rich state)).count = 3) (selected : Fin n)
    (hPivot : (prepare (terminalInput request rich state)).pivot = some selected) : Checked :=
  let prepared := prepare (terminalInput request rich state)
  ⟨BinaryTerminalGroupInputs.castMixed hCount prepared.mixed,
    mixed_canonical_forward hCount _ (prepared.mixed_canonical (terminal_canonical request rich state) selected hPivot),
    mixed_admissible_forward hCount _ (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared
      (terminal_canonical request rich state) (terminal_admissible request rich N bits state h) selected hPivot)⟩

theorem cached_heights {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N → Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (hCount : (prepare (terminalInput request rich state)).count = 3) (selected : Fin n)
    (hPivot : (prepare (terminalInput request rich state)).pivot = some selected) :
    MixedHeights (cached request rich N bits state h hCount selected hPivot).input (inputHeight request) :=
  mixed_heights_cast hCount _ _ (cached_mixed_heights request rich N bits state h selected hPivot)

theorem cached_bounds {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N → Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (hCount : (prepare (terminalInput request rich state)).count = 3) (selected : Fin n)
    (hPivot : (prepare (terminalInput request rich state)).pivot = some selected)
    (K : ℕ) (scalar : Fin K → Bool) (pos : ℕ) (hp : pos ≤ N) :
    let checked := cached request rich N bits state h hCount selected hPivot
    let s := inputHeight request
    (BinaryReflectedSetupWork.prepareWithWork checked.ordered).2 ≤ BinaryReflectedSetupWork.bound s ∧
    (∀ hg : BinaryFourParentCompiler.gluingCase checked.ordered = true,
      (checked.gluing hg K N scalar bits).2 ≤ BinaryGluingDrawWork.bound s K N ∧
      (checked.gluingIndexed hg K N scalar bits pos hp).2 ≤ BinaryGluingDrawWork.partialBound s K (N - pos)) ∧
    (∀ hg : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true,
      (checked.smallUniform hg K N scalar bits pos hp).2 ≤ BinarySmallUniformDrawWork.bound s K (N - pos) ∧
      (BinaryReflectedSetupWork.capacityWithWork (BinaryReflectedFourSetup.prepare checked.ordered)).2 ≤
        3 * (12000 * (2 + 2 * expressionHeightBudget s 14) ^ 3)) :=
  (cached request rich N bits state h hCount selected hPivot).bounds _ (inputHeight_two request)
    (cached_heights request rich N bits state h hCount selected hPivot) K N scalar bits pos hp

end Blotto.BinaryCachedFourBranchWork
