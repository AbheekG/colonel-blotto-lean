import Blotto.GeneralPaperNativeSamplerViewAndLaw

/-! Actual common-word returns draw with a compact local reference.
The draw height ledger excludes accuracy encoding length. Canonical Nash,
every-output hard budgets, real/fast-bit work, rational output and exact
fair-bit counts refer to the same actual stored sampler. -/
namespace Blotto.GeneralPaperNativeDrawHeadline
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperNativeWorkingSpaceHeadline (epsilon epsilon_positive)
open GeneralPaperNativeSamplerViewAndLaw GeneralPaperStoredStrategySampler
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

noncomputable def returned (model : RationalCostModel) (C d : ℕ) (p : Problem) : GeneralPaperClosedStrategyDriver.Prepared p.n :=
  (GeneralPaperClosedStrategyDriver.bit model (word model C d p) (word model C d p) (word model C d p)
    p.words p.values p.selector p.correct p.budget p.budget_valid).1

noncomputable def drawReference (model : RationalCostModel) (C d : ℕ) (p : Problem) : ℕ :=
  GeneralPaperClosedBitSampling.reference p.n (returned model C d p).raw.strategies.original.reduced.m (returned model C d p).raw.exponent

def drawLog (p : Problem) : ℕ := GeneralPaperSamplingFastBitBound.epsilonLog p.n (epsilon p) (originalInputSize p)

def drawScale (p : Problem) : ℚ := (p.n:ℚ)*((originalInputSize p:ℚ)+GeneralPaperRealHeadlineParameters.nStar p.n (epsilon p)/epsilon p)

theorem budget_height_original (p : Problem) : RationalHeight p.budget (originalInputSize p) :=
  (budget_height p).mono (by unfold originalInputSize;omega)

theorem returned_exponent (model : RationalCostModel) (C d : ℕ) (p : Problem) : (returned model C d p).raw.exponent=exponent p :=
  native_exponent (word model C d p) p

theorem returned_reduced (model : RationalCostModel) (C d : ℕ) (p : Problem) :
    (returned model C d p).raw.strategies.original.reduced=reduced model p := by
  let W := word model C d p
  change (GeneralPaperOriginalStrategyDriver.bit model W W W (GeneralPaperBinaryAccuracy.prepare (fun w => w) W p.words).1
    p.values p.selector p.correct p.budget p.budget_valid).1.original.reduced=reduced model p
  rw [GeneralPaperOriginalStrategyDriver.bit_original,native_exponent W p,GeneralPaperOriginalSourceDataCalibration.reduced_models]
  rfl

theorem draw_reference_local (model : RationalCostModel) (C d : ℕ) (p : Problem) :
    drawReference model C d p=GeneralPaperClosedBitSampling.reference p.n (reduced model p).m (exponent p) := by
  unfold drawReference
  rw [returned_reduced,returned_exponent]

theorem native_draw_contract {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (p : Problem) (hOne : epsilon p<1) :
    let actual := returned model C d p
    let o := actual.raw.strategies.original.reduced
    let k := actual.raw.exponent
    let H := GeneralPaperSourcePairAnchorHeights.width o.m k
    let A := drawReference model C d p
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
          p.n*(1+2*GeneralPaperClosedBitSampling.outputHeight o (originalInputSize p) H) := by
  let W := word model C d p
  obtain ⟨sampler,hSampler,hOutput⟩ := GeneralPaperSamplingFastBitBound.bit_return_rate hg W W W p.words p.values p.selector p.correct
    p.budget p.budget_valid (originalInputSize p) (budget_height_original p)
  obtain ⟨other,hOther,hBit⟩ := GeneralPaperSamplingFastBitBound.epsilon_bit_draw hg W W W p.words (epsilon p) (epsilon_positive p) hOne rfl
    p.values p.selector p.correct p.budget p.budget_valid (originalInputSize p) (budget_height_original p)
  have he : other=sampler := Option.some.inj (hOther.symm.trans hSampler)
  subst other
  have hReal := native_arithmetic_draw_work model W W W p.words (epsilon p) rfl p.values p.selector p.correct p.budget p.budget_valid sampler hSampler
  have hGbit := native_epsilon_at_draw_reference true model.rat (drawReference model C d p) model W W W p.words
    (epsilon p) (epsilon_positive p) hOne rfl p.values p.selector p.correct p.budget p.budget_valid sampler hSampler
  have hGreal := native_epsilon_at_draw_reference false (fun _ => 1) 1 model W W W p.words
    (epsilon p) (epsilon_positive p) hOne rfl p.values p.selector p.correct p.budget p.budget_valid sampler hSampler
  refine ⟨sampler,hSampler,hGbit,hGreal,?_⟩
  intro reciprocal fresh
  have h := hBit reciprocal fresh
  have ho := hOutput reciprocal fresh
  refine ⟨hReal reciprocal fresh,?_,h.2,logarithmic_bits false (fun _ => 1) 1 model sampler reciprocal fresh,ho.2.1,ho.2.2.1⟩
  exact h.1.trans_eq (by unfold drawScale drawLog;ring)

end Blotto.GeneralPaperNativeDrawHeadline
