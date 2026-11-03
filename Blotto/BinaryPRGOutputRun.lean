import Blotto.BinaryPRGEmissionRun
import Blotto.BinaryPRGFallbackInventory
import Blotto.BinaryPRGCachedRequest

/-! One actual original-request execution joins retained resource/terminal/
route arithmetic, selected global B-zero construction, original scaling and
stored coordinate framing. Every original byte/law/budget/Nash scope remains.
The ledger combines proved arithmetic primitives with labelled table/payload/
coordinate visits; input/seed/header/control/bookkeeping and full model/physical
execution and space remain separate obligations. -/

namespace Blotto.BinaryPRGOutputRun
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGResourceWork
open BinaryPRGOutputPrimitiveWork BinaryCachedGroupInputHeight
open MeasureTheory BinaryFactoryHeight

structure Ledger where
  sampling : BinaryPRGEmissionRun.Ledger
  fallback : BinaryPRGFallbackInventory.Inventory
  scaling : ℕ
  coordinateFraming : ℕ

def Ledger.recorded (ledger : Ledger) : ℕ := ledger.sampling.recorded + ledger.fallback.writes +
  ledger.fallback.wordCells + ledger.scaling + ledger.coordinateFraming

def fixedSample {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K N : ℕ)
    (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable n SignedWord × Ledger :=
  let result := BinaryPRGEmissionRun.run request rich K N outer scalar bits
  match result.1.1 with
  | some row => (row,⟨result.2,⟨0,0⟩,0,0⟩)
  | none =>
      let fallback := BinaryPRGFallbackInventory.prepare (resourceInput request rich)
      (fallback.1,⟨result.2,fallback.2,0,0⟩)

theorem fixedSample_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K N : ℕ)
    (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedSample request rich K N outer scalar bits).1 = (BinaryPRGEmissionRun.fixedSample request rich K N outer scalar bits).1 := by
  unfold fixedSample BinaryPRGEmissionRun.fixedSample
  dsimp only
  cases he : (BinaryPRGEmissionRun.run request rich K N outer scalar bits).1.1 <;> rfl

theorem fixedSample_sampling {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K N : ℕ)
    (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedSample request rich K N outer scalar bits).2.sampling = (BinaryPRGEmissionRun.run request rich K N outer scalar bits).2 := by
  unfold fixedSample
  dsimp only
  split <;> rfl

def fallbackBound (n s : ℕ) : ℕ := n + n * (2 * (1 + 2 * s) + 1)

theorem fixedSample_fallback_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K N : ℕ)
    (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedSample request rich K N outer scalar bits).2.fallback.writes + (fixedSample request rich K N outer scalar bits).2.fallback.wordCells ≤
      fallbackBound n (inputHeight request) := by
  have hb := BinaryPRGFallbackInventory.request_prepare_bound request rich
  unfold fixedSample
  dsimp only
  split
  · exact Nat.zero_le _
  · unfold fallbackBound
    exact Nat.add_le_add hb.1.le hb.2

def innerSample {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ) (outer : Fin K → Bool)
    (bits : Fin (RationalLottoResourceSystem.innerBitBudget n K) → Bool) : FixedArrayTable n SignedWord × Ledger :=
  fixedSample request rich K (RationalLottoResourceSystem.coinBitBudget n K) outer
    (secondBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K bits)
    (firstBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K bits)

def sample {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : FixedArrayTable n SignedWord × Ledger :=
  innerSample request rich K (secondBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits)
    (firstBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits)

theorem sample_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    (sample request rich K bits).1 = (BinaryPRGCachedPrimitiveRun.sample request rich K bits).1 :=
  (fixedSample_state request rich K _ _ _ _).trans
    ((BinaryPRGEmissionRun.sample_state request rich K bits).trans (BinaryPRGCachedPrimitiveRun.sample_state request rich K bits).symm)

noncomputable def samplingBound {n : ℕ} (request : BinaryPRGRequest.Request n) (K : ℕ) : ℕ :=
  (7554000 * n + 96000) * (request.source.originalInputWordWidth + 2) ^ 3 +
    52 * RationalLottoResourceSystem.coinBitBudget n K * (request.source.originalInputWordWidth + 2) +
      BinaryCachedTerminalEmissionRun.bound n (BinaryCachedTerminalPrimitiveRun.requestHeight request) K
        (RationalLottoResourceSystem.coinBitBudget n K)

theorem terminal_bound_mono (n s K : ℕ) {a b : ℕ} (h : a ≤ b) :
    BinaryCachedTerminalEmissionRun.bound n s K a ≤ BinaryCachedTerminalEmissionRun.bound n s K b := by
  unfold BinaryCachedTerminalEmissionRun.bound BinaryCachedTerminalPrimitiveRun.bound
    BinaryGroupRetainedPrimitiveRun.descriptorDrawBound BinaryGroupRetainedPrimitiveRun.mixedBound
    BinaryFourSpecRetainedWork.runBound BinaryFourOrderedRetainedWork.runBound BinarySmallRetainedPrimitiveWork.runBound
    BinarySmallRetainedPrimitiveWork.rootBound BinarySmallRootPrimitiveRun.rootBound BinarySmallUniformFactoryDraw.bound BinarySmallUniformDrawWork.bound
    BinaryReflectedFactoryRun.bound BinaryReflectedMeasuredRun.bound BinaryReflectedResourceWork.bound
    BinaryReflectedPreparedDraw.bound BinaryReflectedCategoricalWork.bound BinaryGluingDrawWork.partialBound
    BinaryStoredSegmentChoiceWork.selectionBound
  unfold BinaryGroupRetainedPrimitiveRun.descriptorDrawBound BinaryStoredCoinIndexedWork.bound BinaryStoredSegmentChoiceWork.selectionBound
  dsimp only
  gcongr

theorem sample_sampling_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    (sample request rich K bits).2.sampling.recorded ≤ samplingBound request K := by
  let inner := firstBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits
  let outer := secondBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits
  let scalar := secondBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner
  let choice := firstBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner
  have hr := BinaryPRGEmissionRun.run_recorded_bound request rich K (RationalLottoResourceSystem.coinBitBudget n K) outer scalar choice
  have hm := terminal_bound_mono n (BinaryCachedTerminalPrimitiveRun.requestHeight request) K
    (Nat.sub_le (RationalLottoResourceSystem.coinBitBudget n K) (resourceWork request rich (RationalLottoResourceSystem.coinBitBudget n K) choice).1.2)
  change (fixedSample request rich K _ outer scalar choice).2.sampling.recorded ≤ _
  rw [fixedSample_sampling]
  unfold samplingBound
  exact hr.trans (Nat.add_le_add_left hm _)

theorem sample_fallback_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    (sample request rich K bits).2.fallback.writes + (sample request rich K bits).2.fallback.wordCells ≤ fallbackBound n (inputHeight request) :=
  fixedSample_fallback_bound request rich K _ _ _ _

def originalSample {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) : FixedArrayTable n SignedWord × Ledger :=
  let normalized := sample request rich request.precision bits
  let scaled := rescaleWithWork request.prepared.original.a normalized.1
  (scaled.1,{normalized.2 with scaling := scaled.2})

theorem originalSample_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    (originalSample request rich bits).1 = (BinaryPRGCachedPrimitiveRun.originalSample request rich bits).1 := by
  unfold originalSample BinaryPRGCachedPrimitiveRun.originalSample
  dsimp only
  rw [rescaleWithWork_state,sample_state]

theorem originalSample_scaling_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    (originalSample request rich bits).2.scaling ≤ n * opcodeBound (normalizedHeight request request.precision) := by
  unfold originalSample
  dsimp only
  rw [sample_state]
  exact requestScaling_bound request rich request.precision bits

theorem originalSample_fullBudget {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    FullBudget (if rich then (value request.prepared.original.a : ℝ) else (value request.prepared.original.b : ℝ))
      (fun j => (value ((originalSample request rich bits).1.read j) : ℝ)) := by
  rw [originalSample_state]
  exact BinaryPRGCachedPrimitiveRun.originalSample_budget request rich bits

def output {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) : List Bool × Ledger :=
  let row := originalSample request rich bits
  let frame := BinaryStoredRowFrame.row row.1
  let visits := BinaryStoredRowFrameWork.rowCoordinateVisits row.1
  (frame,{row.2 with coordinateFraming := visits})

theorem output_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    (output request rich bits).1 = BinaryPRGCachedRequest.output request rich bits := by
  unfold output BinaryPRGCachedRequest.output
  dsimp only
  rw [originalSample_state,BinaryPRGCachedPrimitiveRun.originalSample_state,BinaryPRGCachedSampler.originalSample_state]

theorem output_length_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    (output request rich bits).1.length ≤ 2 * binaryWordWidth n + 1 + n * (4 * outputWidth request + 3) := by
  unfold output
  dsimp only
  rw [originalSample_state]
  exact requestFrame_length_bound request rich bits

theorem output_coordinateFraming_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    (output request rich bits).2.coordinateFraming ≤ 4 * (2 * binaryWordWidth n + 1 + n * (4 * outputWidth request + 3)) + 2 * n := by
  unfold output
  dsimp only
  rw [originalSample_state]
  exact requestFrame_coordinateVisits_bound request rich bits

noncomputable def bound {n : ℕ} (request : BinaryPRGRequest.Request n) : ℕ :=
  samplingBound request request.precision + fallbackBound n (inputHeight request) +
    n * opcodeBound (normalizedHeight request request.precision) +
      (4 * (2 * binaryWordWidth n + 1 + n * (4 * outputWidth request + 3)) + 2 * n)

theorem output_recorded_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) : (output request rich bits).2.recorded ≤ bound request := by
  have hs := sample_sampling_bound request rich request.precision bits
  have hf := sample_fallback_bound request rich request.precision bits
  have hc := originalSample_scaling_bound request rich bits
  have he := output_coordinateFraming_bound request rich bits
  change (sample request rich request.precision bits).2.sampling.recorded ≤ _ at hs
  change (sample request rich request.precision bits).2.fallback.writes + (sample request rich request.precision bits).2.fallback.wordCells ≤ _ at hf
  change (sample request rich request.precision bits).2.sampling.recorded + (sample request rich request.precision bits).2.fallback.writes +
    (sample request rich request.precision bits).2.fallback.wordCells + (originalSample request rich bits).2.scaling + (output request rich bits).2.coordinateFraming ≤ _
  unfold bound
  omega

def run (rich : Bool) (request seed : List Bool) : Option (List Bool × Ledger) :=
  (BinaryPRGRequest.read request).bind (fun parsed =>
    if parsed.2 = [] then
      (RationalPRGBinaryRequest.seedTable (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 parsed.1.2.precision) seed).map
        (fun table => output parsed.1.2 rich table.read)
    else none)

theorem run_state (rich : Bool) (request seed : List Bool) :
    (run rich request seed).map Prod.fst = BinaryPRGCachedRequest.run rich request seed := by
  unfold run BinaryPRGCachedRequest.run
  simp only [Option.map_bind]
  apply congrArg (Option.bind (BinaryPRGRequest.read request))
  funext parsed
  simp only [Function.comp_def]
  by_cases h : parsed.2 = []
  · simp only [h,ite_true,Option.map_map,Function.comp_def,output_state]
  · simp only [h,ite_false,Option.map_none]

theorem run_recorded_bound (rich : Bool) (request seed : List Bool) (returned : List Bool × Ledger)
    (h : run rich request seed = some returned) :
    ∃ parsed : Σ n, BinaryPRGRequest.Request n,
      BinaryPRGRequest.read request = some (parsed,[]) ∧ returned.2.recorded ≤ bound parsed.2 := by
  unfold run at h
  obtain ⟨parsed,hParsed,hLater⟩ := Option.bind_eq_some_iff.mp h
  split at hLater
  · rename_i hEmpty
    obtain ⟨table,hSeed,hOutput⟩ := Option.map_eq_some_iff.mp hLater
    subst returned
    refine ⟨parsed.1,?_,output_recorded_bound parsed.1.2 rich table.read⟩
    exact hParsed.trans (congrArg some (show parsed = (parsed.1,[]) from Prod.ext rfl hEmpty))
  · cases hLater

theorem run_returned_budget (rich : Bool) (request seed : List Bool) (returned : List Bool × Ledger)
    (h : run rich request seed = some returned) :
    ∃ parsed : Σ n, BinaryPRGRequest.Request n,
      RationalPRGBinaryRequest.readWords request = some ((⟨parsed.1,parsed.2.source⟩ : Σ n, RationalPRGOriginalInput n),parsed.2.accuracy,[]) ∧
      RationalPRGBinaryRequest.ReturnedBudget parsed.1 (if rich then parsed.2.source.a else parsed.2.source.b) returned.1 := by
  have he : BinaryPRGCachedRequest.run rich request seed = some returned.1 := by
    rw [← run_state,h,Option.map_some]
  exact BinaryPRGCachedRequest.run_returned_budget rich request seed returned.1 he

noncomputable def law {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) : Mixed n :=
  (fairBitLaw (RationalLottoResourceSystem.sampleBitBudget n request.precision)).map
    (fun bits j => (value ((originalSample request rich bits).1.read j) : ℝ))

theorem law_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) : law request rich = BinaryPRGCachedPrimitiveRun.law request rich := by
  unfold law BinaryPRGCachedPrimitiveRun.law
  congr 1
  funext bits j
  rw [originalSample_state]

theorem law_regrets {n : ℕ} (request : BinaryPRGRequest.Request n) :
    regret request.source.realValues (request.source.a : ℝ) (law request true) (law request false) < request.accuracy.numeric.real ∧
    regret request.source.realValues (request.source.b : ℝ) (law request false) (law request true) < request.accuracy.numeric.real := by
  rw [law_state,law_state]
  exact BinaryPRGCachedPrimitiveRun.law_regrets request

end Blotto.BinaryPRGOutputRun
