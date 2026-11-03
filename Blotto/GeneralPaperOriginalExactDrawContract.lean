import Blotto.GeneralPaperExactPreparationDraw

/-! Final exact-route original-input bit draw headline on the returned description.
It is expected only in the equal categorical branch. Unequal work and
exact random reads hold for every bit string, with the bounded real draw
cost as well. Accuracy-encoding length occurs in none of these scales. -/
namespace Blotto.GeneralPaperOriginalExactDrawContract
open MeasureTheory
open scoped ENNReal
open GeneralPaperOriginalGameInput GeneralPaperOriginalDrawParameters
open GeneralPaperOriginalDrawTransfers
open GeneralPaperAllBranchBitDispatch (Prepared one)
set_option autoImplicit false
set_option maxHeartbeats 7500000
set_option maxRecDepth 16384

def bound (p : Input) (A e : ℕ) : ℚ := (A : ℚ) * drawScale p * (logarithm p : ℚ) ^ e

def randomScale (p : Input) : ℕ := binaryWordWidth p.n + binaryWordWidth ⌈(epsilon p)⁻¹⌉₊ + 10

def Unequal (model : RationalCostModel) (p : Input) (output : GeneralPaperClosedStrategyDriver.Prepared p.n)
    (A e : ℕ) : Prop :=
  let o := output.raw.strategies.original.reduced
  let k := output.raw.exponent
  let W := GeneralPaperClosedBitSampling.reference p.n o.m k
  let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  ∃ sampler : GeneralPaperStoredStrategySampler.Sampler p.n t.rows (GeneralPaperProxyParameters.prepare o.m k).K,
    output.sampler = some sampler ∧ ∀ poor fresh,
      ((GeneralPaperExactStoredSampler.run true model.rat W model sampler poor fresh).work : ℚ) ≤ bound p A e ∧
      (GeneralPaperExactStoredSampler.run false (fun _ => 1) 1 model sampler poor fresh).work ≤ 131072 * realScale p ∧
      (GeneralPaperExactStoredSampler.run true model.rat W model sampler poor fresh).freshReads =
        Nat.log2 (sampler.controls.rows * GeneralPaperExactStoredSampler.shifts sampler) ∧
      (GeneralPaperExactStoredSampler.run false (fun _ => 1) 1 model sampler poor fresh).freshReads =
        Nat.log2 (sampler.controls.rows * GeneralPaperExactStoredSampler.shifts sampler)

inductive Contract (model : RationalCostModel) (C d K A e : ℕ) (p : Input) : Prepared p.n → Prop
  | oneField (hN : p.n = 1)
      (work : ∀ poor, ((GeneralPaperOneFieldBitOutput.run p poor).work : ℚ) ≤ bound p A e) :
      Contract model C d K A e p (one p hN).1
  | equal (hN : p.n ≠ 1) (hB : p.budget = 1)
      (output : GeneralPaperUnifiedDirectoryInstallation.Installed
        (GeneralPaperStoredSelectedPipeline.width model 1 K (equalInput model p)))
      (work : (∫⁻ trace, ((GeneralPaperStoredSelectedLaw.observed model
        (GeneralPaperStoredSelectedPipeline.width model 1 K (equalInput model p)) output
        (GeneralPaperEqualCopiedPipeline.run model 1 K (equalInput model p)).1.branch trace).work : ℝ≥0∞)
        ∂(GeneralPaperEqualBitBranchDraw.traceLaw (GeneralPaperEqualCopiedPipeline.run model 1 K (equalInput model p)).1.branch :
          Measure (GeneralPaperEqualBitBranchDraw.Trace (GeneralPaperEqualCopiedPipeline.run model 1 K (equalInput model p)).1.branch))) ≤
            ENNReal.ofReal (bound p A e : ℝ))
      (reads : (∫⁻ trace, ((GeneralPaperStoredSelectedLaw.observed model
        (GeneralPaperStoredSelectedPipeline.width model 1 K (equalInput model p)) output
        (GeneralPaperEqualCopiedPipeline.run model 1 K (equalInput model p)).1.branch trace).reads : ℝ≥0∞)
        ∂(GeneralPaperEqualBitBranchDraw.traceLaw (GeneralPaperEqualCopiedPipeline.run model 1 K (equalInput model p)).1.branch :
          Measure (GeneralPaperEqualBitBranchDraw.Trace (GeneralPaperEqualCopiedPipeline.run model 1 K (equalInput model p)).1.branch))) ≤
            (8388608 * randomScale p : ℕ)) : Contract model C d K A e p (.equal _ output)
  | unequal (hN : p.n ≠ 1) (hStrict : p.budget < 1)
      (output : GeneralPaperClosedStrategyDriver.Prepared p.n)
      (sampling : GeneralPaperExactPreparationDraw.Contract model C d (unequalInput p hStrict) output)
      (independent : GeneralPaperExactPreparationDraw.Independent model (unequalInput p hStrict) output)
      (work : Unequal model p output A e) :
      Contract model C d K A e p (.unequal output)

theorem uniform {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (K : ℕ) :
    ∃ A e : ℕ, ∀ (p : Input) (output : Prepared p.n), epsilon p < 1 →
      (GeneralPaperMeasuredBitDispatch.run model K p).1 = some output →
      GeneralPaperOriginalSamplingContract.Contract model C d K p output → Contract model C d K A e p output := by
  obtain ⟨Ae, de, hEqual⟩ := equal_rate model ⟨C, d, hg⟩ K
  let An := 76 * GeneralPaperSamplingFastBitBound.coefficient C d
  let A := Ae + An + 512
  let e := de + d + 2
  refine ⟨A, e, fun p output hOne hReturn hSampling => ?_⟩
  cases hSampling with
  | oneField hN _ _ =>
    exact .oneField hN (fun poor => raise p _ 512 A 0 e (by dsimp [A]; omega) (Nat.zero_le _) (one_rate p poor))
  | equal hN hB output sampling _ =>
    refine .equal hN hB output ?_ ?_
    · have h := raise p _ Ae A de e (by dsimp [A]; omega) (by dsimp [e]; omega) (hEqual p)
      exact sampling.expectedWork.trans (ennreal_bound _ _ h)
    · have hk := equal_exponent model p
      have hn : GeneralPaperEqualSelectedDraw.readsBound p.n (equalInput model p).k ≤ 8388608 * randomScale p := by
        unfold GeneralPaperEqualSelectedDraw.readsBound randomScale
        omega
      exact sampling.expectedReads.trans (by exact_mod_cast hn)
  | unequal hN hStrict output _sampling _ =>
    let q := unequalInput p hStrict
    let actual := GeneralPaperMeasuredUnequalSampling.actual model K q
    have hr : (GeneralPaperMeasuredBitDispatch.run model K p).1 = some (.unequal actual) := by
      rw [GeneralPaperMeasuredBitDispatch.on_unequal model K p hN (ne_of_lt hStrict)]
      rfl
    have he : output = actual := Prepared.unequal.inj (Option.some.inj (hReturn.symm.trans hr))
    subst output
    have hDraw : GeneralPaperExactPreparationDraw.Contract model C d q actual := by
      dsimp only [actual]
      rw [GeneralPaperMeasuredUnequalSampling.data]
      exact GeneralPaperExactPreparationDraw.at_word hg _ q hOne
    have hView := hDraw
    obtain ⟨sampler, hSampler, _, _, hResources⟩ := hView
    refine .unequal hN hStrict actual hDraw
      (GeneralPaperExactPreparationDraw.independent_of_draw q actual hDraw)
      ⟨sampler, hSampler, fun poor fresh => ?_⟩

    have h := hResources poor fresh
    have hn := native_bound p hStrict An (d + 2) _ h.2.1
    have hb := raise p _ An A (d + 2) e (by dsimp [A]; omega) (by dsimp [e]; omega) hn
    exact ⟨hb, h.1, h.2.2.1, h.2.2.2.1⟩

end Blotto.GeneralPaperOriginalExactDrawContract
