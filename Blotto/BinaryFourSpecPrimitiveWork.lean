import Blotto.BinaryFourOrderedPrimitiveWork
import Blotto.BinaryFourSpecFixed
import Blotto.RationalFourSpecHeight

/-! Complete unsorted four-spec fixed/scheduled output retains one native
sorting result and inverse permutation. Its guarded gluing/small producers
preserve exact original rows, whole finite-bit law/CDF and hard budgets. Source
fields derive sorting and selected branch primitive prices; setup/metadata/
physical execution remain separate obligations. -/

namespace Blotto.BinaryFourSpecPrimitiveWork
open MeasureTheory
open BinaryRationalNormalization BinaryRationalEncoding BinaryFourSpecSampler

structure Prepared (original : Input) where
  ordered : BinaryFourParameters.Input
  ordered_correct : ordered = orderedInput original
  canonical : ordered.Canonical
  admissible : BinaryFourAdmissibility.Admissible ordered
  permutation : Equiv.Perm (Fin 4)
  permutation_correct : permutation = BinaryFourSpecSampler.permutation original
  orderWork : ℕ

def prepareOrdered (input : Input) (hC : input.Canonical) (hAd : Admissible input) : Prepared input :=
  let ordered := BinaryFourNativeOrderWork.orderedWithWork input
  have hOrdered : ordered.1.1 = orderedInput input := congrArg Prod.fst (BinaryFourNativeOrderWork.orderedWithWork_state input)
  have hPermutation : ordered.1.2 = permutation input := congrArg Prod.snd (BinaryFourNativeOrderWork.orderedWithWork_state input)
  ⟨ordered.1.1,hOrdered,(by rw [hOrdered]; exact orderedInput_canonical input hC),
    (by rw [hOrdered]; exact orderedInput_admissible input hC hAd),ordered.1.2,hPermutation,ordered.2⟩

theorem prepareOrdered_bound (input : Input) (source : RationalFourSpec) (hC : input.Canonical)
    (hR : input.Refines source) (hAd : Admissible input) (s : ℕ) (hH : source.FieldsHeight s) :
    (prepareOrdered input hC hAd).orderWork ≤ 3 * BinaryFactoryHeight.compareBound s :=
  BinaryFourNativeOrderWork.orderedWithWork_bound input hC s (fun j => by rw [hR.2.1 j]; exact hH.2.1 j)

def Prepared.fixedWithWork {input : Input} (prepared : Prepared input) (K N : ℕ)
    (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable 4 SignedWord × ℕ :=
  let drawn := BinaryFourOrderedPrimitiveWork.fixedSampleWithWork prepared.ordered prepared.canonical prepared.admissible K N outer scalar bits
  (FixedArrayTable.ofFn (fun j => drawn.1.read (prepared.permutation j)),prepared.orderWork + drawn.2)

theorem Prepared.fixedWithWork_state (input : Input) (hC : input.Canonical) (hAd : Admissible input)
    (prepared : Prepared input) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (prepared.fixedWithWork K N outer scalar bits).1 = BinaryFourSpecFixed.sample input hC hAd K N outer scalar bits := by
  cases prepared with
  | mk ordered ordered_correct canonical admissible pi permutation_correct orderWork =>
      cases ordered_correct
      cases permutation_correct
      unfold Prepared.fixedWithWork BinaryFourSpecFixed.sample
      dsimp only
      rw [BinaryFourOrderedPrimitiveWork.fixedSampleWithWork_state]

def fixedSampleWithWork (input : Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable 4 SignedWord × ℕ :=
  (prepareOrdered input hC hAd).fixedWithWork K N outer scalar bits

theorem fixedSampleWithWork_state (input : Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedSampleWithWork input hC hAd K N outer scalar bits).1 = BinaryFourSpecFixed.sample input hC hAd K N outer scalar bits :=
  Prepared.fixedWithWork_state input hC hAd _ K N outer scalar bits

def fixedBound (s K N : ℕ) : ℕ := 3 * BinaryFactoryHeight.compareBound s + BinaryFourOrderedPrimitiveWork.fixedBound s K N

theorem fixedSampleWithWork_bound (input : Input) (source : RationalFourSpec) (hC : input.Canonical)
    (hR : input.Refines source) (hAd : Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedSampleWithWork input hC hAd K N outer scalar bits).2 ≤ fixedBound s K N := by
  let prepared := prepareOrdered input hC hAd
  have hOrder := prepareOrdered_bound input source hC hR hAd s hH
  have hRef : prepared.ordered.Refines source.input := by
    rw [prepared.ordered_correct]
    exact orderedInput_refines input source hC hR
  have hDraw := BinaryFourOrderedPrimitiveWork.fixedSampleWithWork_bound prepared.ordered source.input prepared.canonical hRef
    prepared.admissible s hs hH.input K N outer scalar bits
  exact Nat.add_le_add hOrder hDraw

theorem fixedSampleWithWork_canonical (input : Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    ∀ j, CanonicalWord ((fixedSampleWithWork input hC hAd K N outer scalar bits).1.read j) := by
  rw [fixedSampleWithWork_state]
  exact BinaryFourSpecFixed.sample_canonical input hC hAd K N outer scalar bits

theorem fixedSampleWithWork_value (input : Input) (source : RationalFourSpec) (hC : input.Canonical)
    (hR : input.Refines source) (hAd : Admissible input) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (j : Fin 4) :
    value ((fixedSampleWithWork input hC hAd K N outer scalar bits).1.read j) = source.fixedSample K N outer scalar bits j := by
  rw [fixedSampleWithWork_state]
  exact BinaryFourSpecFixed.sample_value input source hC hR hAd K N outer scalar bits j

theorem fixedSampleWithWork_fullBudget (input : Input) (source : RationalFourSpec) (hC : input.Canonical)
    (hR : input.Refines source) (hAd : Admissible input) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    FullBudget (source.B : ℝ) (fun j => (value ((fixedSampleWithWork input hC hAd K N outer scalar bits).1.read j) : ℝ)) := by
  have hRow : (fun j => (value ((fixedSampleWithWork input hC hAd K N outer scalar bits).1.read j) : ℝ)) =
      fun j => (source.fixedSample K N outer scalar bits j : ℝ) := by
    funext j
    rw [fixedSampleWithWork_value input source hC hR hAd K N outer scalar bits j]
  rw [hRow]
  exact source.fixedSample_fullBudget K N outer scalar bits

def sampleWithWork (input : Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ)
    (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) : FixedArrayTable 4 SignedWord × ℕ :=
  let inner := firstBitBlock (RationalFourInput.innerBitBudget K) K bits
  let outer := secondBitBlock (RationalFourInput.innerBitBudget K) K bits
  fixedSampleWithWork input hC hAd K (RationalFourInput.coinBitBudget K) outer
    (secondBitBlock (RationalFourInput.coinBitBudget K) K inner)
    (firstBitBlock (RationalFourInput.coinBitBudget K) K inner)

theorem sampleWithWork_state (input : Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ)
    (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) :
    (sampleWithWork input hC hAd K bits).1 = BinaryFourSpecSampler.sample input hC hAd K bits := by
  unfold sampleWithWork
  rw [fixedSampleWithWork_state]
  rfl

def bound (s K : ℕ) : ℕ := fixedBound s K (RationalFourInput.coinBitBudget K)

theorem sampleWithWork_bound (input : Input) (source : RationalFourSpec) (hC : input.Canonical)
    (hR : input.Refines source) (hAd : Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) :
    (sampleWithWork input hC hAd K bits).2 ≤ bound s K :=
  fixedSampleWithWork_bound input source hC hR hAd s hs hH K _ _ _ _

theorem sampleWithWork_canonical (input : Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ)
    (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) :
    ∀ j, CanonicalWord ((sampleWithWork input hC hAd K bits).1.read j) := by
  rw [sampleWithWork_state]
  exact BinaryFourSpecSampler.sample_canonical input hC hAd K bits

theorem sampleWithWork_fullBudget (input : Input) (source : RationalFourSpec) (hC : input.Canonical)
    (hR : input.Refines source) (hAd : Admissible input) (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) :
    FullBudget (source.B : ℝ) (fun j => (value ((sampleWithWork input hC hAd K bits).1.read j) : ℝ)) := by
  rw [sampleWithWork_state]
  exact BinaryFourSpecSampler.sample_fullBudget input source hC hR hAd K bits

noncomputable def sampleLaw (input : Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ) : Mixed 4 :=
  (fairBitLaw (RationalFourInput.sampleBitBudget K)).map (fun bits j => (value ((sampleWithWork input hC hAd K bits).1.read j) : ℝ))

theorem sampleLaw_eq (input : Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ) :
    sampleLaw input hC hAd K = BinaryFourSpecSampler.sampleLaw input hC hAd K := by
  unfold sampleLaw BinaryFourSpecSampler.sampleLaw
  congr 1
  funext bits j
  rw [sampleWithWork_state]

theorem sampleLaw_CDF_error (input : Input) (source : RationalFourSpec) (hC : input.Canonical)
    (hR : input.Refines source) (hAd : Admissible input) (K : ℕ) :
    CDFClose (sampleLaw input hC hAd K) source.real.law (5 / (2 * (2 : ℝ) ^ K)) := by
  rw [sampleLaw_eq]
  exact BinaryFourSpecSampler.sampleLaw_CDF_error input source hC hR hAd K

end Blotto.BinaryFourSpecPrimitiveWork
