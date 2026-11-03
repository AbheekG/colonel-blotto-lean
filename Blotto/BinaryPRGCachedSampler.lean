import Blotto.BinaryCachedTerminalRun
import Blotto.BinaryCachedTerminalWork

/-! The complete original-budget PRG sampler uses one resource result and one
cached terminal preparation, then the retained flat seed layout and global
fallback. Ledger fields record resource work and cached preparation arithmetic;
table/control/copy, descriptors, draw/emission/scaling/interface and physical
backend/storage prices remain separate. The cached complete output is exactly
the retained request draw on every seed, including both exhaustion stages. -/

namespace Blotto.BinaryPRGCachedSampler
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGResourceWork BinaryPRGResourceHandoff BinaryPRGTerminalWork

structure Ledger where
  resource : BinaryGeneralResourceExecution.Charge
  classificationPacking : ℕ
  routeDivisions : ℕ
  pivotDivision : ℕ

def run {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (Option (FixedArrayTable n SignedWord) × ℕ) × Ledger :=
  let observed := resourceWork request rich N bits
  match hs : observed.1.1 with
  | none => ((none, observed.1.2), ⟨observed.2, 0, 0, 0⟩)
  | some state =>
      let input := terminalInput request rich state
      let prepared := BinaryCachedTerminalPreparation.prepare input
      let later := BinaryCachedTerminalRun.runPrepared prepared (terminal_canonical request rich state)
        (terminal_admissible request rich N bits state hs) K N outer scalar bits observed.1.2
        (resourceWork_position request rich N bits)
      (later, ⟨observed.2, prepared.prefixWork,
        BinaryCachedTerminalWork.routeArithmeticWork prepared, BinaryCachedTerminalWork.pivotArithmeticWork prepared⟩)

theorem run_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (run request rich K N outer scalar bits).1 =
      (BinaryPRGResourceHandoff.run request rich K N outer scalar bits).1 := by
  unfold run BinaryPRGResourceHandoff.run
  dsimp only
  split
  · rename_i hNone
    split
    · rfl
    · rename_i state hOther
      cases hNone.symm.trans hOther
  · rename_i state hSome
    rw [BinaryCachedTerminalRun.runPrepared_state]
    split
    · rename_i hNone
      cases hSome.symm.trans hNone
    · rename_i other hOther
      have he : state = other := Option.some.inj (hSome.symm.trans hOther)
      subst other
      rfl

theorem run_resource_ledger {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (run request rich K N outer scalar bits).2.resource = (resourceWork request rich N bits).2 := by
  unfold run
  dsimp only
  split <;> rfl

theorem run_prefix_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (run request rich K N outer scalar bits).2.classificationPacking ≤
      166000 * n * (request.source.originalInputWordWidth + 2) ^ 3 := by
  unfold run
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i state hs
    exact BinaryTerminalClassificationWork.reached_classifyAndPack_boolean_bound request rich N bits state hs

theorem run_ledger_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (run request rich K N outer scalar bits).2.resource.booleanWork +
      (run request rich K N outer scalar bits).2.classificationPacking ≤
        7266000 * n * (request.source.originalInputWordWidth + 2) ^ 3 +
          52 * N * (request.source.originalInputWordWidth + 2) := by
  have hr := resource_boolean_bound request rich N bits
  have hp := run_prefix_bound request rich K N outer scalar bits
  rw [run_resource_ledger]
  nlinarith

theorem run_preparation_arithmetic_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (run request rich K N outer scalar bits).2.classificationPacking +
      (run request rich K N outer scalar bits).2.routeDivisions +
      (run request rich K N outer scalar bits).2.pivotDivision ≤
        (454000 * n + 96000) * (request.source.originalInputWordWidth + 2) ^ 3 := by
  unfold run
  dsimp only
  split
  · simp
  · rename_i state hs
    exact BinaryCachedTerminalWork.reached_arithmeticWork_bound request rich N bits state hs

theorem run_total_recorded_arithmetic_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (run request rich K N outer scalar bits).2.resource.booleanWork +
      (run request rich K N outer scalar bits).2.classificationPacking +
      (run request rich K N outer scalar bits).2.routeDivisions +
      (run request rich K N outer scalar bits).2.pivotDivision ≤
        (7554000 * n + 96000) * (request.source.originalInputWordWidth + 2) ^ 3 +
          52 * N * (request.source.originalInputWordWidth + 2) := by
  have hp := run_preparation_arithmetic_bound request rich K N outer scalar bits
  have hr := resource_boolean_bound request rich N bits
  rw [← run_resource_ledger request rich K N outer scalar bits] at hr
  nlinarith

def fixedSample {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable n SignedWord × Ledger :=
  let result := run request rich K N outer scalar bits
  (result.1.1.getD (BinaryLottoSampler.fallback (resourceInput request rich)), result.2)

theorem fixedSample_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedSample request rich K N outer scalar bits).1 =
      (BinaryPRGResourceHandoff.fixedSample request rich K N outer scalar bits).1 := by
  unfold fixedSample BinaryPRGResourceHandoff.fixedSample
  dsimp only
  rw [run_state]

def innerSample {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ)
    (outer : Fin K → Bool) (bits : Fin (RationalLottoResourceSystem.innerBitBudget n K) → Bool) :
    FixedArrayTable n SignedWord × Ledger :=
  fixedSample request rich K (RationalLottoResourceSystem.coinBitBudget n K) outer
    (secondBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K bits)
    (firstBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K bits)

def sample {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : FixedArrayTable n SignedWord × Ledger :=
  innerSample request rich K
    (secondBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits)
    (firstBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits)

theorem sample_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    (sample request rich K bits).1 = (BinaryPRGResourceHandoff.sample request rich K bits).1 :=
  fixedSample_state _ _ _ _ _ _ _

def originalSample {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    FixedArrayTable n SignedWord × Ledger :=
  let normalized := sample request rich request.precision bits
  (BinaryPRGOriginalSampler.rescale request.prepared.original.a normalized.1, normalized.2)

theorem originalSample_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    (originalSample request rich bits).1 = if rich then request.richSample bits else request.poorSample bits := by
  have he := BinaryPRGResourceHandoff.originalSample_state request rich bits
  unfold originalSample
  unfold BinaryPRGResourceHandoff.originalSample at he
  dsimp only at he ⊢
  rw [sample_state]
  exact he

theorem originalSample_budget {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
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
    law request rich = BinaryPRGResourceHandoff.law request rich := by
  have he : (fun bits j => (value ((originalSample request rich bits).1.read j) : ℝ)) =
      fun bits j => (value ((BinaryPRGResourceHandoff.originalSample request rich bits).1.read j) : ℝ) := by
    funext bits j
    rw [originalSample_state, BinaryPRGResourceHandoff.originalSample_state]
  unfold law BinaryPRGResourceHandoff.law
  rw [he]

theorem law_regrets {n : ℕ} (request : BinaryPRGRequest.Request n) :
    regret request.source.realValues (request.source.a : ℝ) (law request true) (law request false) < request.accuracy.numeric.real ∧
    regret request.source.realValues (request.source.b : ℝ) (law request false) (law request true) < request.accuracy.numeric.real := by
  rw [law_state, law_state]
  exact BinaryPRGResourceHandoff.law_regrets request

end Blotto.BinaryPRGCachedSampler
