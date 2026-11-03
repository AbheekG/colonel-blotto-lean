import Blotto.BinarySmallFixedPrimitiveWork
import Blotto.BinaryGluingDrawWork
import Blotto.BinaryFourNativeOrderWork

/-! The measured ordered four producer retains one native regime guard and
joins either complete gluing output or complete small output with its exact
fallback. Both equality and strict regimes retain original word/law/budget
semantics and source-derived recorded primitive prices. Cached setup and whole
computational-model costs remain separate joins. -/

namespace Blotto.BinaryFourOrderedPrimitiveWork
open MeasureTheory
open BinaryRationalNormalization BinaryRationalEncoding BinaryFourAdmissibility

def fixedSampleWithWork (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable 4 SignedWord × ℕ :=
  let guard := BinaryFourNativeOrderWork.guardWithWork input
  if hg : guard.1 = true then
    let drawn := BinaryGluingDrawWork.fixedSampleWithWork input hC
      (gluing_guard input hC hAd ((BinaryFourNativeOrderWork.guardWithWork_state input).symm.trans hg)) K N scalar bits
    (drawn.1,guard.2 + drawn.2)
  else
    let drawn := BinarySmallFixedPrimitiveWork.fixedSampleWithWork input hC
      (small_guard input hC hAd (fun h => hg ((BinaryFourNativeOrderWork.guardWithWork_state input).trans h))) K N outer scalar bits
    (drawn.1,guard.2 + drawn.2)

theorem fixedSampleWithWork_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedSampleWithWork input hC hAd K N outer scalar bits).1 = BinaryFourSampler.fixedSample input hC hAd K N outer scalar bits := by
  unfold fixedSampleWithWork
  dsimp only
  split
  · rename_i hg
    have hOld := (BinaryFourNativeOrderWork.guardWithWork_state input).symm.trans hg
    unfold BinaryFourSampler.fixedSample
    rw [dite_eq_left hOld]
    exact BinaryGluingDrawWork.fixedSampleWithWork_state input hC _ K N scalar bits
  · rename_i hg
    have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := fun h => hg ((BinaryFourNativeOrderWork.guardWithWork_state input).trans h)
    unfold BinaryFourSampler.fixedSample
    rw [dite_eq_right hOld]
    exact BinarySmallFixedPrimitiveWork.fixedSampleWithWork_state input hC _ K N outer scalar bits

theorem guard_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (s : ℕ) (hH : source.FieldsHeight s) :
    (BinaryFourNativeOrderWork.guardWithWork input).2 ≤ BinaryFourNativeOrderWork.guardBound (max s 3) := by
  have h := BinaryFourNativeOrderWork.input_height_of_refines input source hR s hH
  have hm := le_max_left s 3
  exact BinaryFourNativeOrderWork.guardWithWork_bound input hC _ (le_max_right _ _)
    ⟨h.1.mono hm,h.2.1.mono hm,h.2.2.1.mono hm,h.2.2.2.1.mono hm,h.2.2.2.2.1.mono hm,h.2.2.2.2.2.mono hm⟩

def fixedBound (s K N : ℕ) : ℕ := BinaryFourNativeOrderWork.guardBound (max s 3) +
  BinaryGluingDrawWork.bound s K N + BinarySmallFixedPrimitiveWork.fixedBound s K N

theorem fixedSampleWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : Admissible input) (s : ℕ) (hs : 2 ≤ s)
    (hH : source.FieldsHeight s) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedSampleWithWork input hC hAd K N outer scalar bits).2 ≤ fixedBound s K N := by
  have hGuard := guard_bound input source hC hR s hH
  unfold fixedSampleWithWork
  dsimp only
  split
  · rename_i hg
    have hOld := (BinaryFourNativeOrderWork.guardWithWork_state input).symm.trans hg
    have hCase := (BinaryFourParentCompiler.gluingCase_iff input source hC hR).mp hOld
    have hDraw := BinaryGluingDrawWork.fixedSampleWithWork_bound input source hC hR
      (gluing_guard input hC hAd hOld) hCase s hs hH K N scalar bits
    dsimp only
    unfold fixedBound
    omega
  · rename_i hg
    have hOld : ¬BinaryFourParentCompiler.gluingCase input = true := fun h => hg ((BinaryFourNativeOrderWork.guardWithWork_state input).trans h)
    have hCase := lt_of_not_ge (fun h => hg ((BinaryFourNativeOrderWork.guardWithWork_state input).trans
      ((BinaryFourParentCompiler.gluingCase_iff input source hC hR).mpr h)))
    have hDraw := BinarySmallFixedPrimitiveWork.fixedSampleWithWork_bound input source hC hR
      (small_guard input hC hAd hOld) hCase s hs hH K N outer scalar bits
    dsimp only
    unfold fixedBound
    omega

theorem fixedSampleWithWork_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    ∀ j, CanonicalWord ((fixedSampleWithWork input hC hAd K N outer scalar bits).1.read j) := by
  rw [fixedSampleWithWork_state]
  exact BinaryFourSampler.fixedSample_canonical input hC hAd K N outer scalar bits

def sampleWithWork (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ)
    (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) : FixedArrayTable 4 SignedWord × ℕ :=
  let inner := firstBitBlock (RationalFourInput.innerBitBudget K) K bits
  let outer := secondBitBlock (RationalFourInput.innerBitBudget K) K bits
  fixedSampleWithWork input hC hAd K (RationalFourInput.coinBitBudget K) outer
    (secondBitBlock (RationalFourInput.coinBitBudget K) K inner)
    (firstBitBlock (RationalFourInput.coinBitBudget K) K inner)

theorem sampleWithWork_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ)
    (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) :
    (sampleWithWork input hC hAd K bits).1 = BinaryFourSampler.sample input hC hAd K bits :=
  fixedSampleWithWork_state input hC hAd K _ _ _ _

def bound (s K : ℕ) : ℕ := fixedBound s K (RationalFourInput.coinBitBudget K)

theorem sampleWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : Admissible input) (s : ℕ) (hs : 2 ≤ s)
    (hH : source.FieldsHeight s) (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) :
    (sampleWithWork input hC hAd K bits).2 ≤ bound s K :=
  fixedSampleWithWork_bound input source hC hR hAd s hs hH K _ _ _ _

theorem sampleWithWork_fullBudget (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : Admissible input) (K : ℕ)
    (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) :
    FullBudget (source.B : ℝ) (fun j => (value ((sampleWithWork input hC hAd K bits).1.read j) : ℝ)) := by
  rw [sampleWithWork_state]
  exact BinaryFourSampler.sample_fullBudget input source hC hR hAd K bits

end Blotto.BinaryFourOrderedPrimitiveWork
