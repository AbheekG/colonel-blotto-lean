import Blotto.GeneralPaperEnlargedReferencePreparationTime

/-! The complete native draw contract at any preparation word. Drawing uses
only the actual returned sampler and its compact local reference; original
budget precision remains additive and accuracy encoding length is absent. -/
namespace Blotto.GeneralPaperArbitraryPreparationDraw
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters
open GeneralPaperNativeWorkingSpaceHeadline (epsilon epsilon_positive)
open GeneralPaperNativeSamplerViewAndLaw GeneralPaperStoredStrategySampler
open GeneralPaperNativeDrawHeadline (drawScale drawLog budget_height_original)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def returned (model : RationalCostModel) (W : ℕ) (p : Problem) : GeneralPaperClosedStrategyDriver.Prepared p.n :=
  (GeneralPaperClosedStrategyDriver.bit model W W W
    p.words p.values p.selector p.correct p.budget p.budget_valid).1

def drawReference (model : RationalCostModel) (W : ℕ) (p : Problem) : ℕ :=
  GeneralPaperClosedBitSampling.reference p.n (returned model W p).raw.strategies.original.reduced.m (returned model W p).raw.exponent

theorem returned_exponent (model : RationalCostModel) (W : ℕ) (p : Problem) : (returned model W p).raw.exponent=exponent p :=
  native_exponent (W) p

theorem returned_reduced (model : RationalCostModel) (W : ℕ) (p : Problem) :
    (returned model W p).raw.strategies.original.reduced=reduced model p := by
  change (GeneralPaperOriginalStrategyDriver.bit model W W W (GeneralPaperBinaryAccuracy.prepare (fun w => w) W p.words).1
    p.values p.selector p.correct p.budget p.budget_valid).1.original.reduced=reduced model p
  rw [GeneralPaperOriginalStrategyDriver.bit_original,native_exponent W p,GeneralPaperOriginalSourceDataCalibration.reduced_models]
  rfl

theorem draw_reference_local (model : RationalCostModel) (W : ℕ) (p : Problem) :
    drawReference model W p=GeneralPaperClosedBitSampling.reference p.n (reduced model p).m (exponent p) := by
  unfold drawReference
  rw [returned_reduced,returned_exponent]


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
      GeneralPaperClosedStrategyEquilibrium.Guarantee true model.rat A model p.selector.values (p.budget:ℝ) (epsilon p:ℝ) sampler ∧
      GeneralPaperClosedStrategyEquilibrium.Guarantee false (fun _ => 1) 1 model p.selector.values (p.budget:ℝ) (epsilon p:ℝ) sampler ∧
      ∀ (reciprocal : Bool) (fresh : Fin (sampler.controls.rowBits+sampler.controls.shiftBits) → Bool),
        (run false (fun _ => 1) 1 model sampler reciprocal fresh).work≤131072*(p.n+binaryWordWidth ⌈(epsilon p)⁻¹⌉₊) ∧
        ((run true model.rat A model sampler reciprocal fresh).work:ℚ)≤
          ((76*GeneralPaperSamplingFastBitBound.coefficient C d:ℕ):ℚ)*drawScale p*(drawLog p:ℚ)^(d+2) ∧
        (run true model.rat A model sampler reciprocal fresh).freshReads=Nat.log2 (sampler.controls.rows*sampler.controls.shifts) ∧
        (run false (fun _ => 1) 1 model sampler reciprocal fresh).freshReads=Nat.log2 (sampler.controls.rows*sampler.controls.shifts) ∧
        (∀ j,RationalHeight ((run true model.rat A model sampler reciprocal fresh).output.read j) (GeneralPaperClosedBitSampling.outputHeight o (originalInputSize p) H)) ∧
        GeneralPaperClosedBitSampling.outputBits (run true model.rat A model sampler reciprocal fresh).output≤
          p.n*(1+2*GeneralPaperClosedBitSampling.outputHeight o (originalInputSize p) H)

theorem at_word {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W : ℕ) (p : Problem) (hOne : epsilon p < 1) : Contract model C d p (returned model W p) := by
  obtain ⟨sampler,hSampler,hOutput⟩ := GeneralPaperSamplingFastBitBound.bit_return_rate hg W W W p.words p.values p.selector p.correct
    p.budget p.budget_valid (originalInputSize p) (budget_height_original p)
  obtain ⟨other,hOther,hBit⟩ := GeneralPaperSamplingFastBitBound.epsilon_bit_draw hg W W W p.words (epsilon p) (epsilon_positive p) hOne rfl
    p.values p.selector p.correct p.budget p.budget_valid (originalInputSize p) (budget_height_original p)
  have he : other=sampler := Option.some.inj (hOther.symm.trans hSampler)
  subst other
  have hReal := native_arithmetic_draw_work model W W W p.words (epsilon p) rfl p.values p.selector p.correct p.budget p.budget_valid sampler hSampler
  have hGbit := native_epsilon_at_draw_reference true model.rat (drawReference model W p) model W W W p.words
    (epsilon p) (epsilon_positive p) hOne rfl p.values p.selector p.correct p.budget p.budget_valid sampler hSampler
  have hGreal := native_epsilon_at_draw_reference false (fun _ => 1) 1 model W W W p.words
    (epsilon p) (epsilon_positive p) hOne rfl p.values p.selector p.correct p.budget p.budget_valid sampler hSampler
  refine ⟨sampler,hSampler,hGbit,hGreal,?_⟩
  intro reciprocal fresh
  have h := hBit reciprocal fresh
  have ho := hOutput reciprocal fresh
  refine ⟨hReal reciprocal fresh,?_,h.2,logarithmic_bits false (fun _ => 1) 1 model sampler reciprocal fresh,ho.2.1,ho.2.2.1⟩
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
    let D := sampler.controls.rowBits + sampler.controls.shiftBits
    MeasureTheory.Measure.map (fun fresh =>
      ((fun j => ((run true model.rat A model sampler false (firstBitBlock D D fresh)).output.read j : ℝ)),
       (fun j => ((run true model.rat A model sampler true (secondBitBlock D D fresh)).output.read j : ℝ))))
      (fairBitLaw (D + D) : MeasureTheory.Measure (Fin (D + D) → Bool)) =
      (law true model.rat A model sampler false : MeasureTheory.Measure (Allocation p.n)).prod
        (law true model.rat A model sampler true : MeasureTheory.Measure (Allocation p.n))

theorem independent_of_draw {model : RationalCostModel} {C d : ℕ} (p : Problem)
    (actual : GeneralPaperClosedStrategyDriver.Prepared p.n) (hDraw : Contract model C d p actual) :
    Independent model p actual := by
  obtain ⟨sampler, hSampler, _⟩ := hDraw
  exact ⟨sampler, hSampler, GeneralPaperStoredStrategySampler.independent_players true model.rat _ model sampler⟩

end Blotto.GeneralPaperArbitraryPreparationDraw
