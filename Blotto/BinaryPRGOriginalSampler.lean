import Blotto.BinaryPRGPreparation
import Blotto.BinaryAccuracyWords

/-! Both prepared Boolean PRG draws return stored canonical whole arrays at
the original budgets. Every seed agrees with the retained original rational
sampler, hence both independent fair-bit laws preserve the canonical continuous
Nash guarantees. The draw consumes only prepared words and Boolean seeds;
semantic source witnesses are erased proofs. Complete costs remain separate. -/

namespace Blotto.BinaryPRGOriginalSampler
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryPRGPreparation

def rescale {n : ℕ} (budget : SignedWord) (row : FixedArrayTable n SignedWord) : FixedArrayTable n SignedWord :=
  FixedArrayTable.ofFn (fun j => apply .mul budget (row.read j))

def richSample {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : FixedArrayTable n SignedWord :=
  rescale prepared.original.a (richDraw prepared h K bits)

def poorSample {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : FixedArrayTable n SignedWord :=
  rescale prepared.original.a (poorDraw prepared h K bits)

theorem richSample_canonical {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    ∀ j, CanonicalWord ((richSample prepared h K bits).read j) := by
  intro j
  rw [richSample, rescale, FixedArrayTable.read_ofFn]
  exact BinaryPRGRecognition.opcode_canonical .mul _ _ h.2.1.1 (richDraw_canonical prepared h K bits j)

theorem poorSample_canonical {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    ∀ j, CanonicalWord ((poorSample prepared h K bits).read j) := by
  intro j
  rw [poorSample, rescale, FixedArrayTable.read_ofFn]
  exact BinaryPRGRecognition.opcode_canonical .mul _ _ h.2.1.1 (poorDraw_canonical prepared h K bits j)

theorem richSample_refines {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    BinaryTerminalPartialRun.sourceRow (richSample prepared h K bits) =
      (prepared.original.source h.2.2).richSample K bits := by
  funext j
  have hd := congrFun (richDraw_refines prepared h K bits) j
  change value ((richDraw prepared h K bits).read j) = _ at hd
  change value ((richSample prepared h K bits).read j) = _
  rw [richSample, rescale, FixedArrayTable.read_ofFn,
    apply_value .mul _ _ h.2.1.1.1 (richDraw_canonical prepared h K bits j).1, hd,
    RationalPRGOriginalInput.richSample_apply]
  rfl

theorem poorSample_refines {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    BinaryTerminalPartialRun.sourceRow (poorSample prepared h K bits) =
      (prepared.original.source h.2.2).poorSample K bits := by
  funext j
  have hd := congrFun (poorDraw_refines prepared h K bits) j
  change value ((poorDraw prepared h K bits).read j) = _ at hd
  change value ((poorSample prepared h K bits).read j) = _
  rw [poorSample, rescale, FixedArrayTable.read_ofFn,
    apply_value .mul _ _ h.2.1.1.1 (poorDraw_canonical prepared h K bits j).1, hd,
    RationalPRGOriginalInput.poorSample_apply]
  rfl

theorem richSample_fullBudget {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    FullBudget (value prepared.original.a : ℝ)
      (fun j => (value ((richSample prepared h K bits).read j) : ℝ)) := by
  have he := congrArg (fun row : Fin n → ℚ => fun j => (row j : ℝ)) (richSample_refines prepared h K bits)
  exact he.symm ▸ (prepared.original.source h.2.2).richSample_fullBudget K bits

theorem poorSample_fullBudget {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    FullBudget (value prepared.original.b : ℝ)
      (fun j => (value ((poorSample prepared h K bits).read j) : ℝ)) := by
  have he := congrArg (fun row : Fin n → ℚ => fun j => (row j : ℝ)) (poorSample_refines prepared h K bits)
  exact he.symm ▸ (prepared.original.source h.2.2).poorSample_fullBudget K bits

noncomputable def richSampleLaw {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ) : Mixed n :=
  (fairBitLaw (RationalLottoResourceSystem.sampleBitBudget n K)).map
    (fun bits j => (value ((richSample prepared h K bits).read j) : ℝ))

noncomputable def poorSampleLaw {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ) : Mixed n :=
  (fairBitLaw (RationalLottoResourceSystem.sampleBitBudget n K)).map
    (fun bits j => (value ((poorSample prepared h K bits).read j) : ℝ))

theorem richSampleLaw_refines {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ) :
    richSampleLaw prepared h K = (prepared.original.source h.2.2).richSampleLaw K := by
  unfold richSampleLaw RationalPRGOriginalInput.richSampleLaw
  congr 1
  funext bits j
  exact congrArg (fun q : ℚ => (q : ℝ)) (congrFun (richSample_refines prepared h K bits) j)

theorem poorSampleLaw_refines {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ) :
    poorSampleLaw prepared h K = (prepared.original.source h.2.2).poorSampleLaw K := by
  unfold poorSampleLaw RationalPRGOriginalInput.poorSampleLaw
  congr 1
  funext bits j
  exact congrArg (fun q : ℚ => (q : ℝ)) (congrFun (poorSample_refines prepared h K bits) j)

theorem sample_regrets {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ) :
    regret (prepared.original.source h.2.2).realValues (value prepared.original.a : ℝ)
      (richSampleLaw prepared h K) (poorSampleLaw prepared h K) ≤ 5 / (2 : ℝ) ^ K ∧
    regret (prepared.original.source h.2.2).realValues (value prepared.original.b : ℝ)
      (poorSampleLaw prepared h K) (richSampleLaw prepared h K) ≤ 5 / (2 : ℝ) ^ K := by
  rw [richSampleLaw_refines, poorSampleLaw_refines]
  exact (prepared.original.source h.2.2).sample_regrets K

theorem rational_accuracy_regrets {n : ℕ} (prepared : Prepared n) (h : prepared.Valid)
    (epsilon : ℚ) (he : 0 < epsilon) :
    regret (prepared.original.source h.2.2).realValues (value prepared.original.a : ℝ)
      (richSampleLaw prepared h (rationalAccuracyPrecision epsilon))
      (poorSampleLaw prepared h (rationalAccuracyPrecision epsilon)) < (epsilon : ℝ) ∧
    regret (prepared.original.source h.2.2).realValues (value prepared.original.b : ℝ)
      (poorSampleLaw prepared h (rationalAccuracyPrecision epsilon))
      (richSampleLaw prepared h (rationalAccuracyPrecision epsilon)) < (epsilon : ℝ) := by
  rw [richSampleLaw_refines, poorSampleLaw_refines]
  exact (prepared.original.source h.2.2).rational_accuracy_regrets epsilon he

def richApproximateSample {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (accuracy : BinaryAccuracyWords)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n accuracy.precision) → Bool) : FixedArrayTable n SignedWord :=
  richSample prepared h accuracy.precision bits

def poorApproximateSample {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (accuracy : BinaryAccuracyWords)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n accuracy.precision) → Bool) : FixedArrayTable n SignedWord :=
  poorSample prepared h accuracy.precision bits

theorem stored_accuracy_regrets {n : ℕ} (prepared : Prepared n) (h : prepared.Valid)
    (accuracy : BinaryAccuracyWords) :
    regret (prepared.original.source h.2.2).realValues (value prepared.original.a : ℝ)
      (richSampleLaw prepared h accuracy.precision) (poorSampleLaw prepared h accuracy.precision) < accuracy.numeric.real ∧
    regret (prepared.original.source h.2.2).realValues (value prepared.original.b : ℝ)
      (poorSampleLaw prepared h accuracy.precision) (richSampleLaw prepared h accuracy.precision) < accuracy.numeric.real := by
  rw [richSampleLaw_refines, poorSampleLaw_refines, accuracy.precision_eq]
  exact accuracy.numeric.original_regrets (prepared.original.source h.2.2)

end Blotto.BinaryPRGOriginalSampler
