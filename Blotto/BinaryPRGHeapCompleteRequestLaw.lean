import Blotto.BinaryPRGHeapCompleteRequestWork

/-! Independent finite-bit whole-allocation laws of the request with the
physical general and reflected resource phases. Exact sample equality preserves original
hard budgets and both continuous-deviation regret bounds. -/

namespace Blotto.BinaryPRGHeapCompleteRequestLaw
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryLottoResourceInput

def sample {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : FixedArrayTable n SignedWord :=
  let inner := firstBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits
  let outer := secondBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits
  let scalar := secondBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner
  let choice := firstBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner
  (BinaryPRGHeapCompleteRequestWork.fixedSample (BinarySeedLookupTree.prepare (List.ofFn choice))
    request rich K outer scalar).1

theorem sample_erasure {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    sample request rich K bits = BinaryPRGWordControllerRequest.sample request rich K bits :=
  BinaryPRGHeapCompleteRequestWork.fixedSample_erasure _ _ _ _ _ _

def originalSample {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    FixedArrayTable n SignedWord :=
  let normalized := sample request rich request.precision bits
  FixedArrayTable.ofFn (fun j => BinaryQuadraticData.apply .mul
    request.prepared.original.a (normalized.read j))

theorem originalSample_erasure {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    originalSample request rich bits = BinaryPRGWordControllerRequest.originalSample request rich bits := by
  unfold originalSample BinaryPRGWordControllerRequest.originalSample
  rw [sample_erasure]

theorem originalSample_fullBudget {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    FullBudget (if rich then (value request.prepared.original.a : ℝ)
      else (value request.prepared.original.b : ℝ))
      (fun j => (value ((originalSample request rich bits).read j) : ℝ)) := by
  rw [originalSample_erasure]
  exact BinaryPRGWordControllerRequest.originalSample_fullBudget request rich bits

noncomputable def law {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) : Mixed n :=
  (fairBitLaw (RationalLottoResourceSystem.sampleBitBudget n request.precision)).map
    (fun bits j => (value ((originalSample request rich bits).read j) : ℝ))

theorem law_erasure {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) :
    law request rich = BinaryPRGWordControllerRequest.law request rich := by
  unfold law BinaryPRGWordControllerRequest.law
  simp only [originalSample_erasure]

theorem law_regrets {n : ℕ} (request : BinaryPRGRequest.Request n) :
    regret request.source.realValues (request.source.a : ℝ) (law request true) (law request false) <
      request.accuracy.numeric.real ∧
    regret request.source.realValues (request.source.b : ℝ) (law request false) (law request true) <
      request.accuracy.numeric.real := by
  rw [law_erasure,law_erasure]
  exact BinaryPRGWordControllerRequest.law_regrets request

end Blotto.BinaryPRGHeapCompleteRequestLaw
