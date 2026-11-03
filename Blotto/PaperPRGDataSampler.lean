import Blotto.PaperPRGConcretePriceCoverage
import Blotto.PaperPRGAccuracyPrecision

/-! Runtime entry points contain only game/precision/header data and random
bits. They materialize normalized arrays and use their stored readers, without
executing a cost oracle or price interpreter. The preceding priced source
procedures erase to these exact data, including every cap/fallback path.
-/

namespace Blotto.PaperPRGDataSampler
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem cache_ext {n : ℕ} {i : RationalLottoResourceSystem n}
    (first second : PaperPRGNormalizedCache.Cache i) (hB : first.budget=second.budget)
    (hL : first.lengths=second.lengths) (hR : first.resources=second.resources) : first=second := by
  cases first
  cases second
  cases hB
  cases hL
  cases hR
  rfl

def prepare {n : ℕ} (i : RationalPRGOriginalInput n) (rich : Bool) :
    PaperPRGNormalizedCache.Cache (PaperPRGNormalizedCache.source i rich) :=
  let ratio := i.b/i.a
  let lengths := FixedArrayTable.ofFn (fun j => (2:ℚ)*i.values j)
  let resources := if rich then lengths else FixedArrayTable.ofFn (fun j => ratio*lengths.read j)
  have hLengths : lengths.read=(PaperPRGNormalizedCache.source i rich).length := by
    funext j
    rw [FixedArrayTable.read_ofFn]
    cases rich <;> rfl
  have hResources : resources.read=(PaperPRGNormalizedCache.source i rich).initial := by
    dsimp only [resources]
    cases rich with
    | false =>
        simp only [Bool.false_eq_true,ite_false]
        funext j
        rw [FixedArrayTable.read_ofFn,congrFun hLengths j]
        rfl
    | true => exact hLengths
  ⟨if rich then 1 else ratio,lengths,resources,by cases rich <;> rfl,hLengths,hResources⟩

theorem prepare_erases {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W : ℕ) (rich : Bool) :
    (PaperPRGNormalizedCache.build i model primitive W rich).1=prepare i rich := by
  apply cache_ext
  · rfl
  · unfold PaperPRGNormalizedCache.build prepare
    dsimp only
    rw [PaperIndexedArrayConstruction.run_data]
  · unfold PaperPRGNormalizedCache.build prepare
    dsimp only
    cases rich <;> simp only [Bool.false_eq_true,ite_false,ite_true,PaperIndexedArrayConstruction.run_data]

def sample {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) : RationalResourceArray n :=
  let cached := prepare p.source rich
  let normalized := cached.system.storedPaperSample p.precision bits
  normalized.scaled p.source.a

theorem sample_data {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    sample p rich bits=NativePRGPreparedSampler.sample p rich bits := by
  unfold sample
  dsimp only
  rw [(prepare p.source rich).system_eq]
  cases rich <;> rfl

theorem priced_sample_erases {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    (PaperPRGCachedDraw.sample p model primitive rich bits).1=sample p rich bits := by
  rw [PaperPRGCachedDraw.sample_data,sample_data]

def output {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) : List Bool :=
  ReferenceStoredRowFrame.frame p.bytes (sample p rich bits)

theorem output_data {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    output p rich bits=NativePRGPreparedSampler.output p rich bits := by
  unfold output NativePRGPreparedSampler.output
  rw [sample_data]

theorem priced_output_erases {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    PaperPRGCachedDraw.output p model primitive rich bits=output p rich bits := by
  rw [PaperPRGCachedDraw.output_data,output_data]

theorem output_budget {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    RationalPRGBinaryRequest.ReturnedBudget n (if rich then p.source.a else p.source.b) (output p rich bits) := by
  rw [output_data]
  exact NativePRGPreparedSampler.output_read_budget p rich bits

theorem output_length {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    (output p rich bits).length ≤ p.bytes.length+2*n*PRGPaperDrawCost.outputWidth p.source p.precision+n := by
  rw [output_data]
  exact PRGPaperDrawCost.output_length p rich bits

noncomputable def law {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (rich : Bool) : Mixed n :=
  (fairBitLaw (RationalLottoResourceSystem.sampleBitBudget n p.precision)).map
    (fun bits => (sample p rich bits).realAllocation)

theorem law_data {n : ℕ} (p : NativePRGPreparedSampler.Prepared n) (rich : Bool) :
    law p rich=if rich then p.source.storedRichLaw p.precision else p.source.storedPoorLaw p.precision := by
  unfold law
  simp_rw [sample_data]
  cases rich <;> rfl

theorem accuracy_regrets {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput) :
    regret i.realValues (i.a:ℝ) (law (NativePRGPreparedSampler.ofInput i a.precision) true)
      (law (NativePRGPreparedSampler.ofInput i a.precision) false) < a.real ∧
    regret i.realValues (i.b:ℝ) (law (NativePRGPreparedSampler.ofInput i a.precision) false)
      (law (NativePRGPreparedSampler.ofInput i a.precision) true) < a.real := by
  simp only [law_data,ite_true,Bool.false_eq_true,ite_false]
  exact NativePRGPreparedSampler.prepared_accuracy_regrets i a

def run (rich : Bool) (request seed : List Bool) : Option (List Bool) :=
  (NativePRGRequestPreparation.prepare request).bind (fun prepared =>
    (RationalPRGBinaryRequest.seedTable (RationalLottoResourceSystem.sampleBitBudget prepared.1 prepared.2.precision) seed).map
      (fun table => output prepared.2 rich table.read))

theorem run_data (rich : Bool) (request seed : List Bool) :
    run rich request seed=NativePRGRequestPreparation.run rich request seed := by
  simp only [run,NativePRGRequestPreparation.run,output_data]

theorem run_refines (rich : Bool) (request seed : List Bool) :
    run rich request seed=RationalPRGBinaryRequest.run rich request seed :=
  (run_data rich request seed).trans (NativePRGRequestPreparation.run_refines rich request seed)

end Blotto.PaperPRGDataSampler
