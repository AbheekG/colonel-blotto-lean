import Blotto.BinaryPRGRecognition
import Blotto.BinaryLottoSampler
import Blotto.RationalPRGOriginalSampler

/-! Original stored PRG words produce both normalized native Lotto inputs.
The ratio, doubled lengths and poor initial resources are prepared once and
retained as arrays. Source construction/refinement occurs only in Prop proofs;
neither sampler receives a rational source or a terminal factory at runtime.
Input framing, accuracy parsing and complete preparation/runtime/space prices
remain distinct obligations. -/

namespace Blotto.BinaryPRGPreparation
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryPRGRecognition

structure Prepared (n : ℕ) where
  original : BinaryPRGRecognition.Input n
  ratio : SignedWord
  lengths : FixedArrayTable n SignedWord
  poorResources : FixedArrayTable n SignedWord

def prepare {n : ℕ} (input : BinaryPRGRecognition.Input n) : Prepared n :=
  let ratio := apply .div input.b input.a
  let lengths := FixedArrayTable.ofFn (fun j => apply .mul two (input.values.read j))
  let poorResources := FixedArrayTable.ofFn (fun j => apply .mul ratio (lengths.read j))
  ⟨input, ratio, lengths, poorResources⟩

def Prepared.rich {n : ℕ} (prepared : Prepared n) : BinaryLottoResourceInput.Input n :=
  ⟨one, prepared.lengths, prepared.lengths⟩

def Prepared.poor {n : ℕ} (prepared : Prepared n) : BinaryLottoResourceInput.Input n :=
  ⟨prepared.ratio, prepared.lengths, prepared.poorResources⟩

def Prepared.Valid {n : ℕ} (prepared : Prepared n) : Prop :=
  prepared = prepare prepared.original ∧ prepared.original.Canonical ∧ prepared.original.Checks

theorem prepare_valid {n : ℕ} (input : BinaryPRGRecognition.Input n)
    (hC : input.Canonical) (h : input.Checks) : (prepare input).Valid := ⟨rfl, hC, h⟩

theorem prepare_original {n : ℕ} (input : BinaryPRGRecognition.Input n) :
    (prepare input).original = input := rfl

def prepareChecked {n : ℕ} (input : BinaryPRGRecognition.Input n) (hC : input.Canonical) :
    Option {prepared : Prepared n // prepared.Valid} :=
  if h : checkBool input = true then
    some ⟨prepare input, prepare_valid input hC ((checkBool_iff input hC).mp h)⟩
  else none

theorem prepareChecked_isSome {n : ℕ} (input : BinaryPRGRecognition.Input n) (hC : input.Canonical) :
    (prepareChecked input hC).isSome = true ↔ input.Checks := by
  by_cases hb : checkBool input = true
  · have hi := (checkBool_iff input hC).mp hb
    simp [prepareChecked, hb, hi]
  · have hi : ¬input.Checks := fun hi => hb ((checkBool_iff input hC).mpr hi)
    simp [prepareChecked, hb, hi]

theorem prepareChecked_data {n : ℕ} (input : BinaryPRGRecognition.Input n) (hC : input.Canonical)
    (result : {prepared : Prepared n // prepared.Valid}) (h : prepareChecked input hC = some result) :
    result.val = prepare input := by
  unfold prepareChecked at h
  split at h
  · cases Option.some.inj h
    rfl
  · cases h

theorem ratio_canonical {n : ℕ} (input : BinaryPRGRecognition.Input n) (hC : input.Canonical) :
    CanonicalWord (prepare input).ratio := opcode_canonical .div _ _ hC.2.1 hC.1

theorem ratio_value {n : ℕ} (input : BinaryPRGRecognition.Input n) (hC : input.Canonical) :
    value (prepare input).ratio = value input.b / value input.a :=
  apply_value .div _ _ hC.2.1.1 hC.1.1

theorem lengths_canonical {n : ℕ} (input : BinaryPRGRecognition.Input n) (hC : input.Canonical) :
    ∀ j, CanonicalWord ((prepare input).lengths.read j) := by
  intro j
  change CanonicalWord ((FixedArrayTable.ofFn _).read j)
  rw [FixedArrayTable.read_ofFn]
  exact opcode_canonical .mul _ _ two_canonical (hC.2.2 j)

theorem lengths_value {n : ℕ} (input : BinaryPRGRecognition.Input n) (hC : input.Canonical) (j : Fin n) :
    value ((prepare input).lengths.read j) = 2 * value (input.values.read j) := by
  change value ((FixedArrayTable.ofFn _).read j) = _
  rw [FixedArrayTable.read_ofFn, apply_value .mul _ _ two_canonical.1 (hC.2.2 j).1, two_value]
  rfl

theorem poorResources_canonical {n : ℕ} (input : BinaryPRGRecognition.Input n) (hC : input.Canonical) :
    ∀ j, CanonicalWord ((prepare input).poorResources.read j) := by
  intro j
  change CanonicalWord ((FixedArrayTable.ofFn _).read j)
  rw [FixedArrayTable.read_ofFn]
  exact opcode_canonical .mul _ _ (ratio_canonical input hC) (lengths_canonical input hC j)

theorem poorResources_value {n : ℕ} (input : BinaryPRGRecognition.Input n) (hC : input.Canonical) (j : Fin n) :
    value ((prepare input).poorResources.read j) =
      (value input.b / value input.a) * (2 * value (input.values.read j)) := by
  change value ((FixedArrayTable.ofFn _).read j) = _
  rw [FixedArrayTable.read_ofFn]
  change value (apply .mul (prepare input).ratio ((prepare input).lengths.read j)) = _
  rw [apply_value .mul _ _
    (ratio_canonical input hC).1 (lengths_canonical input hC j).1,
    ratio_value input hC, lengths_value input hC j]
  rfl

theorem rich_canonical {n : ℕ} (input : BinaryPRGRecognition.Input n) (hC : input.Canonical) :
    (prepare input).rich.Canonical :=
  ⟨one_canonical, lengths_canonical input hC, lengths_canonical input hC⟩

theorem poor_canonical {n : ℕ} (input : BinaryPRGRecognition.Input n) (hC : input.Canonical) :
    (prepare input).poor.Canonical :=
  ⟨ratio_canonical input hC, lengths_canonical input hC, poorResources_canonical input hC⟩

theorem rich_refines {n : ℕ} (input : BinaryPRGRecognition.Input n)
    (hC : input.Canonical) (h : input.Checks) :
    (prepare input).rich.Refines (input.source h).normalizedInput.richNativeSystem :=
  ⟨one_value, lengths_value input hC, lengths_value input hC⟩

theorem poor_refines {n : ℕ} (input : BinaryPRGRecognition.Input n)
    (hC : input.Canonical) (h : input.Checks) :
    (prepare input).poor.Refines (input.source h).normalizedInput.poorNativeSystem :=
  ⟨ratio_value input hC, lengths_value input hC, poorResources_value input hC⟩

theorem Prepared.rich_canonical {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) :
    prepared.rich.Canonical := by
  rw [h.1]
  exact Blotto.BinaryPRGPreparation.rich_canonical prepared.original h.2.1

theorem Prepared.poor_canonical {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) :
    prepared.poor.Canonical := by
  rw [h.1]
  exact Blotto.BinaryPRGPreparation.poor_canonical prepared.original h.2.1

theorem Prepared.rich_refines {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) :
    prepared.rich.Refines (prepared.original.source h.2.2).normalizedInput.richNativeSystem := by
  rw [show prepared.rich = (prepare prepared.original).rich from congrArg Prepared.rich h.1]
  exact Blotto.BinaryPRGPreparation.rich_refines prepared.original h.2.1 h.2.2

theorem Prepared.poor_refines {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) :
    prepared.poor.Refines (prepared.original.source h.2.2).normalizedInput.poorNativeSystem := by
  rw [show prepared.poor = (prepare prepared.original).poor from congrArg Prepared.poor h.1]
  exact Blotto.BinaryPRGPreparation.poor_refines prepared.original h.2.1 h.2.2

theorem Prepared.rich_admissible {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) :
    BinaryLottoResourceInput.Admissible prepared.rich := by
  exact ⟨(prepared.original.source h.2.2).normalizedInput.richNativeSystem, prepared.rich_refines h⟩

theorem Prepared.poor_admissible {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) :
    BinaryLottoResourceInput.Admissible prepared.poor := by
  exact ⟨(prepared.original.source h.2.2).normalizedInput.poorNativeSystem, prepared.poor_refines h⟩

def richDraw {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : FixedArrayTable n SignedWord :=
  BinaryLottoSampler.sample prepared.rich (prepared.rich_canonical h) (prepared.rich_admissible h) K bits

def poorDraw {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : FixedArrayTable n SignedWord :=
  BinaryLottoSampler.sample prepared.poor (prepared.poor_canonical h) (prepared.poor_admissible h) K bits

theorem richDraw_refines {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    BinaryTerminalPartialRun.sourceRow (richDraw prepared h K bits) =
      (prepared.original.source h.2.2).normalizedInput.richSample K bits := by
  exact BinaryLottoSampler.sample_refines _ _ _ (prepared.rich_refines h) _ K bits

theorem poorDraw_refines {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    BinaryTerminalPartialRun.sourceRow (poorDraw prepared h K bits) =
      (prepared.original.source h.2.2).normalizedInput.poorSample K bits := by
  exact BinaryLottoSampler.sample_refines _ _ _ (prepared.poor_refines h) _ K bits

theorem richDraw_canonical {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    ∀ j, CanonicalWord ((richDraw prepared h K bits).read j) :=
  BinaryLottoSampler.sample_canonical _ _ _ K bits

theorem poorDraw_canonical {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    ∀ j, CanonicalWord ((poorDraw prepared h K bits).read j) :=
  BinaryLottoSampler.sample_canonical _ _ _ K bits

end Blotto.BinaryPRGPreparation
