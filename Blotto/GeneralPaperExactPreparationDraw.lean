import Blotto.GeneralPaperExactSamplerGuarantee

/-! Complete exact-route draw contract at every preparation reference.
Same actual returned sampler: canonical laws, every-path budgets, bounded
real/bit work, rational output, exact bits and independent whole players. -/
namespace Blotto.GeneralPaperExactPreparationDraw
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters
open GeneralPaperNativeWorkingSpaceHeadline (epsilon epsilon_positive)
open GeneralPaperNativeSamplerViewAndLaw GeneralPaperStoredStrategySampler
open GeneralPaperNativeDrawHeadline (drawScale drawLog budget_height_original)
open GeneralPaperArbitraryPreparationDraw (returned drawReference)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def Contract (model : RationalCostModel) (C d : ℕ) (p : Problem)
    (actual : GeneralPaperClosedStrategyDriver.Prepared p.n) : Prop :=
    let o := actual.raw.strategies.original.reduced
    let k := actual.raw.exponent
    let H := GeneralPaperSourcePairAnchorHeights.width o.m k
    let A := GeneralPaperClosedBitSampling.reference p.n o.m k
    ∃ sampler : Sampler p.n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      (GeneralPaperProxyParameters.prepare o.m k).K,
      actual.sampler=some sampler ∧
      GeneralPaperExactSamplerGuarantee.Guarantee true model.rat A model p.selector.values (p.budget:ℝ) (epsilon p:ℝ) sampler ∧
      GeneralPaperExactSamplerGuarantee.Guarantee false (fun _ => 1) 1 model p.selector.values (p.budget:ℝ) (epsilon p:ℝ) sampler ∧
      ∀ (reciprocal : Bool) (fresh : Fin (GeneralPaperExactStoredSampler.bits sampler) → Bool),
        (GeneralPaperExactStoredSampler.run false (fun _ => 1) 1 model sampler reciprocal fresh).work≤131072*(p.n+binaryWordWidth ⌈(epsilon p)⁻¹⌉₊) ∧
        ((GeneralPaperExactStoredSampler.run true model.rat A model sampler reciprocal fresh).work:ℚ)≤
          ((76*GeneralPaperSamplingFastBitBound.coefficient C d:ℕ):ℚ)*drawScale p*(drawLog p:ℚ)^(d+2) ∧
        (GeneralPaperExactStoredSampler.run true model.rat A model sampler reciprocal fresh).freshReads=Nat.log2 (sampler.controls.rows*GeneralPaperExactStoredSampler.shifts sampler) ∧
        (GeneralPaperExactStoredSampler.run false (fun _ => 1) 1 model sampler reciprocal fresh).freshReads=Nat.log2 (sampler.controls.rows*GeneralPaperExactStoredSampler.shifts sampler) ∧
        (∀ j,RationalHeight ((GeneralPaperExactStoredSampler.run true model.rat A model sampler reciprocal fresh).output.read j) (GeneralPaperClosedBitSampling.outputHeight o (originalInputSize p) H)) ∧
        GeneralPaperClosedBitSampling.outputBits (GeneralPaperExactStoredSampler.run true model.rat A model sampler reciprocal fresh).output≤
          p.n*(1+2*GeneralPaperClosedBitSampling.outputHeight o (originalInputSize p) H)

theorem logarithmic_control_bits {n T K : ℕ} (bitModel : Bool) (primitive : ℕ → ℕ)
    (A : ℕ) (model : RationalCostModel) (sampler : Sampler n T K) (poor : Bool)
    (fresh : Fin (GeneralPaperExactStoredSampler.bits sampler) → Bool) :
    (GeneralPaperExactStoredSampler.run bitModel primitive A model sampler poor fresh).freshReads =
      Nat.log2 (sampler.controls.rows * GeneralPaperExactStoredSampler.shifts sampler) := by
  rw [GeneralPaperExactStoredSampler.fresh_reads, sampler.controls.rows_power,
    GeneralPaperExactStoredSampler.shifts_power, ← pow_add, Nat.log2_two_pow]
  rfl

theorem at_word {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W : ℕ) (p : Problem) (hOne : epsilon p < 1) : Contract model C d p (returned model W p) := by
  obtain ⟨sampler,hSampler,hOutput⟩ := GeneralPaperExactSamplerNativeHeadlines.bit_return_rate hg W W W p.words p.values p.selector p.correct
    p.budget p.budget_valid (originalInputSize p) (budget_height_original p)
  obtain ⟨other,hOther,hBit⟩ := GeneralPaperExactSamplerNativeHeadlines.epsilon_bit_draw hg W W W p.words (epsilon p) (epsilon_positive p) hOne rfl
    p.values p.selector p.correct p.budget p.budget_valid (originalInputSize p) (budget_height_original p)
  have he : other=sampler := Option.some.inj (hOther.symm.trans hSampler)
  subst other
  have hReal := GeneralPaperExactSamplerNativeHeadlines.native_arithmetic_draw_work model W W W p.words (epsilon p) rfl p.values p.selector p.correct p.budget p.budget_valid sampler hSampler
  have hGbit := native_epsilon_at_draw_reference true model.rat (drawReference model W p) model W W W p.words
    (epsilon p) (epsilon_positive p) hOne rfl p.values p.selector p.correct p.budget p.budget_valid sampler hSampler
  have hGreal := native_epsilon_at_draw_reference false (fun _ => 1) 1 model W W W p.words
    (epsilon p) (epsilon_positive p) hOne rfl p.values p.selector p.correct p.budget p.budget_valid sampler hSampler
  refine ⟨sampler,hSampler,GeneralPaperExactSamplerGuarantee.of_reference hGbit,GeneralPaperExactSamplerGuarantee.of_reference hGreal,?_⟩
  intro reciprocal fresh
  have h := hBit reciprocal fresh
  have ho := hOutput reciprocal fresh
  refine ⟨hReal reciprocal fresh,?_,h.2,logarithmic_control_bits false (fun _ => 1) 1 model sampler reciprocal fresh,ho.2.1,ho.2.2.1⟩
  exact h.1.trans_eq (by unfold drawScale drawLog;ring)

def Independent (model : RationalCostModel) (p : Problem)
    (actual : GeneralPaperClosedStrategyDriver.Prepared p.n) : Prop :=
  let o := actual.raw.strategies.original.reduced
  let k := actual.raw.exponent
  let A := GeneralPaperClosedBitSampling.reference p.n o.m k
  ∃ sampler : Sampler p.n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      (GeneralPaperProxyParameters.prepare o.m k).K,
    actual.sampler = some sampler ∧
    let D := GeneralPaperExactStoredSampler.bits sampler
    MeasureTheory.Measure.map (fun fresh =>
      ((fun j => ((GeneralPaperExactStoredSampler.run true model.rat A model sampler false (firstBitBlock D D fresh)).output.read j : ℝ)),
       (fun j => ((GeneralPaperExactStoredSampler.run true model.rat A model sampler true (secondBitBlock D D fresh)).output.read j : ℝ))))
      (fairBitLaw (D + D) : MeasureTheory.Measure (Fin (D + D) → Bool)) =
      (law true model.rat A model sampler false : MeasureTheory.Measure (Allocation p.n)).prod
        (law true model.rat A model sampler true : MeasureTheory.Measure (Allocation p.n))

theorem independent_of_draw {model : RationalCostModel} {C d : ℕ} (p : Problem)
    (actual : GeneralPaperClosedStrategyDriver.Prepared p.n) (hDraw : Contract model C d p actual) :
    Independent model p actual := by
  obtain ⟨sampler, hSampler, _⟩ := hDraw
  exact ⟨sampler, hSampler, GeneralPaperExactStoredSampler.independent_players true model.rat _ model sampler⟩

end Blotto.GeneralPaperExactPreparationDraw
