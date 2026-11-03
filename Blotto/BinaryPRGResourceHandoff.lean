import Blotto.BinaryPRGResourceWork

/-! The actual instrumented resource result is retained once and handed to
native terminal sampling with the same cap, reader and absolute position.
Neither exhaustion stage is absorbed. The returned Charge prices only the
resource phase; terminal preparation/sampling/emission still require their own
ledgers and are not zero-priced by this interface. -/

namespace Blotto.BinaryPRGResourceHandoff
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGResourceWork
open BinaryGeneralResourceExecution

theorem resource_success {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state) :
    (BinaryLottoResourceInput.run (resourceInput request rich) (resource_canonical request rich) N bits).1 = some state := by
  rw [← resourceWork_state]
  exact h

def run {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (Option (FixedArrayTable n SignedWord) × ℕ) × Charge :=
  let observed := resourceWork request rich N bits
  match hs : observed.1.1 with
  | none => ((none, observed.1.2), observed.2)
  | some state =>
      let later := BinaryTerminalPartialRun.runIndexed
        (BinaryLottoResourceInput.groupingInput (resourceInput request rich) state)
        (BinaryLottoResourceInput.groupingInput_canonical _ (resource_canonical request rich) state)
        (BinaryLottoResourceInput.reachedGrouping_admissible _ (resource_canonical request rich)
          (resource_admissible request rich) N bits state (resource_success request rich N bits state hs))
        K N outer scalar bits observed.1.2 (resourceWork_position request rich N bits)
      (later, observed.2)

theorem run_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (run request rich K N outer scalar bits).1 =
      BinaryLottoSamplerRun.run (resourceInput request rich) (resource_canonical request rich)
        (resource_admissible request rich) K N outer scalar bits := by
  unfold run BinaryLottoSamplerRun.run
  simp only [resourceWork_state]
  split
  · rename_i hs
    have ho : (BinaryLottoResourceInput.run (resourceInput request rich) (resource_canonical request rich) N bits).1 = none := by
      rw [← resourceWork_state]
      exact hs
    split
    · rfl
    · rename_i state hOld
      cases ho.symm.trans hOld
  · rename_i state hs
    have ho := resource_success request rich N bits state hs
    split
    · rename_i hOld
      cases ho.symm.trans hOld
    · rename_i other hOld
      have he : state = other := Option.some.inj (ho.symm.trans hOld)
      subst other
      rfl

theorem run_resource_charge {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (run request rich K N outer scalar bits).2 = (resourceWork request rich N bits).2 := by
  unfold run
  dsimp only
  split <;> rfl

theorem run_resource_boolean_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (run request rich K N outer scalar bits).2.booleanWork ≤
      7100000 * n * (request.source.originalInputWordWidth + 2) ^ 3 +
        52 * N * (request.source.originalInputWordWidth + 2) := by
  rw [run_resource_charge]
  exact resource_boolean_bound request rich N bits

theorem run_position {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (run request rich K N outer scalar bits).1.2 ≤ N := by
  rw [run_state]
  exact BinaryLottoSamplerRun.run_position _ _ _ K N outer scalar bits

def fixedSample {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable n SignedWord × Charge :=
  let result := run request rich K N outer scalar bits
  (result.1.1.getD (BinaryLottoSampler.fallback (resourceInput request rich)), result.2)

theorem fixedSample_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedSample request rich K N outer scalar bits).1 =
      BinaryLottoSampler.fixedSample (resourceInput request rich) (resource_canonical request rich)
        (resource_admissible request rich) K N outer scalar bits := by
  unfold fixedSample BinaryLottoSampler.fixedSample
  dsimp only
  rw [run_state]

theorem fixedSample_canonical {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    ∀ j, CanonicalWord ((fixedSample request rich K N outer scalar bits).1.read j) := by
  rw [fixedSample_state]
  exact BinaryLottoSampler.fixedSample_canonical _ _ _ K N outer scalar bits

theorem fixedSample_fullBudget {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    FullBudget (value (resourceInput request rich).budget : ℝ)
      (fun j => (value ((fixedSample request rich K N outer scalar bits).1.read j) : ℝ)) := by
  rw [fixedSample_state]
  exact BinaryLottoSampler.fixedSample_fullBudget _ _ _ K N outer scalar bits

def innerSample {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ)
    (outer : Fin K → Bool) (bits : Fin (RationalLottoResourceSystem.innerBitBudget n K) → Bool) :
    FixedArrayTable n SignedWord × Charge :=
  fixedSample request rich K (RationalLottoResourceSystem.coinBitBudget n K) outer
    (secondBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K bits)
    (firstBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K bits)

def sample {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : FixedArrayTable n SignedWord × Charge :=
  innerSample request rich K
    (secondBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits)
    (firstBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits)

theorem sample_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    (sample request rich K bits).1 = BinaryLottoSampler.sample (resourceInput request rich)
      (resource_canonical request rich) (resource_admissible request rich) K bits :=
  fixedSample_state _ _ _ _ _ _ _

theorem sample_resource_boolean_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    (sample request rich K bits).2.booleanWork ≤
      7100000 * n * (request.source.originalInputWordWidth + 2) ^ 3 +
        52 * RationalLottoResourceSystem.coinBitBudget n K * (request.source.originalInputWordWidth + 2) :=
  run_resource_boolean_bound _ _ _ _ _ _ _

def originalSample {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    FixedArrayTable n SignedWord × Charge :=
  let normalized := sample request rich request.precision bits
  (BinaryPRGOriginalSampler.rescale request.prepared.original.a normalized.1, normalized.2)

theorem originalSample_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    (originalSample request rich bits).1 = if rich then request.richSample bits else request.poorSample bits := by
  unfold originalSample
  dsimp only
  rw [sample_state]
  cases rich <;> rfl

theorem originalSample_resource_boolean_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    (originalSample request rich bits).2.booleanWork ≤
      7100000 * n * (request.source.originalInputWordWidth + 2) ^ 3 +
        52 * RationalLottoResourceSystem.coinBitBudget n request.precision * (request.source.originalInputWordWidth + 2) :=
  sample_resource_boolean_bound _ _ _ bits

theorem originalSample_fullBudget {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    FullBudget (if rich then (value request.prepared.original.a : ℝ) else (value request.prepared.original.b : ℝ))
      (fun j => (value ((originalSample request rich bits).1.read j) : ℝ)) := by
  rw [originalSample_state]
  cases rich
  · exact (request.sample_budgets bits).2
  · exact (request.sample_budgets bits).1

noncomputable def law {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) : Mixed n :=
  (fairBitLaw (RationalLottoResourceSystem.sampleBitBudget n request.precision)).map
    (fun bits j => (value ((originalSample request rich bits).1.read j) : ℝ))

theorem law_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) :
    law request rich = if rich then
      BinaryPRGOriginalSampler.richSampleLaw request.prepared request.valid request.precision else
      BinaryPRGOriginalSampler.poorSampleLaw request.prepared request.valid request.precision := by
  have he : (fun bits j => (value ((originalSample request rich bits).1.read j) : ℝ)) =
      fun bits j => (value ((if rich then request.richSample bits else request.poorSample bits).read j) : ℝ) := by
    funext bits j
    rw [originalSample_state]
  unfold law
  rw [he]
  cases rich <;> rfl

theorem law_regrets {n : ℕ} (request : BinaryPRGRequest.Request n) :
    regret request.source.realValues (request.source.a : ℝ) (law request true) (law request false) <
      request.accuracy.numeric.real ∧
    regret request.source.realValues (request.source.b : ℝ) (law request false) (law request true) <
      request.accuracy.numeric.real := by
  rw [law_state, law_state]
  exact request.regrets

end Blotto.BinaryPRGResourceHandoff
