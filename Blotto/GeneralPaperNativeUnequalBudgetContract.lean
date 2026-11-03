import Blotto.GeneralPaperNativeDrawHeadline

/-! The complete actual unequal-budget producer contract: one deterministic
common-word preparation, one retained sampler, all resource headlines,
canonical Nash/hard budgets and independent bounded fresh draws. -/
namespace Blotto.GeneralPaperNativeUnequalBudgetContract
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperNativeWorkingSpaceHeadline (epsilon epsilon_positive paperLog spaceScale)
open GeneralPaperNativeSourceTimeHeadline (timeScale)
open GeneralPaperNativeFramedPreparationTime (frame)
open GeneralPaperNativeReturnedDescriptionHeadline (descriptionScale)
open GeneralPaperNativeDrawHeadline GeneralPaperStoredStrategySampler GeneralPaperOriginalSourceDriverConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

abbrev SamplerFor (model : RationalCostModel) (C d : ℕ) (p : Problem) :=
  Sampler p.n
    (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet (returned model C d p).raw.strategies.original.reduced.m
      (returned model C d p).raw.exponent).lambda (returned model C d p).raw.exponent).rows
    (GeneralPaperProxyParameters.prepare (returned model C d p).raw.strategies.original.reduced.m (returned model C d p).raw.exponent).K

def Drawing (model : RationalCostModel) (C d : ℕ) (p : Problem) (sampler : SamplerFor model C d p) : Prop :=
  let actual := returned model C d p
  let o := actual.raw.strategies.original.reduced
  let k := actual.raw.exponent
  let H := GeneralPaperSourcePairAnchorHeights.width o.m k
  let A := drawReference model C d p
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

def ExecutionSpace (model : RationalCostModel) (C d As es : ℕ) (p : Problem) : Prop :=
  let W := word model C d p
  let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) W p.words).1
  let actual := (GeneralPaperOriginalSourceValuePreparation.run true model W k p.values p.selector p.correct).1
  ∀ (cS : SourceCursor actual.reduced.m k actual.Qv)
    (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor actual.reduced (GeneralPaperOriginalStrategyConstructionStorage.rows k actual.reduced)),
    let observed := GeneralPaperClosedStrategyConstructionStorage.window W
      (GeneralPaperAccuracyStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).1
      (GeneralPaperAccuracyStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).2
      (GeneralPaperAccuracyStrategyConstructionStorage.window model W p.words p.values p.selector p.correct p.budget p.budget_valid cS cD)
    (observed:ℚ)≤(As:ℚ)*spaceScale p*(paperLog p:ℚ)^es ∧ observed<2^W ∧
      GeneralPaperClosedDescriptionStorage.preparedFoot W
        (GeneralPaperClosedStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).1<2^W

def Independent (model : RationalCostModel) (C d : ℕ) (p : Problem) (sampler : SamplerFor model C d p) : Prop :=
  let A := drawReference model C d p
  let D := sampler.controls.rowBits+sampler.controls.shiftBits
  MeasureTheory.Measure.map (fun fresh =>
    ((fun j => ((run true model.rat A model sampler false (firstBitBlock D D fresh)).output.read j:ℝ)),
      (fun j => ((run true model.rat A model sampler true (secondBitBlock D D fresh)).output.read j:ℝ))))
    (fairBitLaw (D+D) : MeasureTheory.Measure (Fin (D+D) → Bool))=
    (law true model.rat A model sampler false : MeasureTheory.Measure (Allocation p.n)).prod
      (law true model.rat A model sampler true : MeasureTheory.Measure (Allocation p.n))

def Contract (model : RationalCostModel) (C d At et As es Ad : ℕ) (p : Problem) : Prop :=
  let W := word model C d p
  ((GeneralPaperClosedStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).2:ℚ)≤
    (At:ℚ)*timeScale p*(paperLog p:ℚ)^et ∧ ExecutionSpace model C d As es p ∧
  ∃ sampler : SamplerFor model C d p,
    (returned model C d p).sampler=some sampler ∧
    (GeneralPaperClosedDescriptionStorage.footprint W sampler:ℚ)≤(Ad:ℚ)*descriptionScale p*(paperLog p:ℚ)^2 ∧
    (GeneralPaperClosedDescriptionStorage.preparedFoot W (returned model C d p):ℚ)≤(Ad:ℚ)*descriptionScale p*(paperLog p:ℚ)^2 ∧
    Drawing model C d p sampler ∧ Independent model C d p sampler

theorem uniform_contract {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ At et As es Ad : ℕ,∀ p : Problem,epsilon p<1 → Contract model C d At et As es Ad p := by
  obtain ⟨At,et,hTime⟩ := GeneralPaperNativePreparationTimeHeadline.native_bit_time_headline hg
  obtain ⟨As,es,hSpace⟩ := GeneralPaperNativeWorkingSpaceHeadline.native_bit_window_headline hg
  obtain ⟨Ad,hDescription⟩ := GeneralPaperNativeReturnedDescriptionHeadline.native_bit_return_description hg
  refine ⟨At,et,As,es,Ad,?_⟩
  intro p hOne
  obtain ⟨sampler,hSampler,hDrawing⟩ := native_draw_contract hg p hOne
  obtain ⟨other,hOther,hFoot,hPrepared⟩ := hDescription p hOne
  have he : other=sampler := Option.some.inj (hOther.symm.trans hSampler)
  subst other
  exact ⟨hTime p hOne,hSpace p hOne,sampler,hSampler,hFoot,hPrepared,hDrawing,
    independent_players true model.rat (drawReference model C d p) model sampler⟩

def FrameSpace (model : RationalCostModel) (C d As es : ℕ) (p : Problem) : Prop :=
  let W := word model C d p
  ∃ parsed,(GeneralPaperBinaryAccuracy.read (fun w => w) W (frame p)).1=some (parsed,[]) ∧ parsed.exponent=exponent p ∧
    let actual := (GeneralPaperOriginalSourceValuePreparation.run true model W parsed.exponent p.values p.selector p.correct).1
    ∀ (cS : SourceCursor actual.reduced.m parsed.exponent actual.Qv)
      (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor actual.reduced (GeneralPaperOriginalStrategyConstructionStorage.rows parsed.exponent actual.reduced)),
      let raw := ((GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W parsed.exponent p.values p.selector p.correct p.budget p.budget_valid).1,([]:List Bool))
      let observed := GeneralPaperClosedStrategyConstructionStorage.frameWindow model W (frame p) p.values p.selector p.correct p.budget p.budget_valid raw
        (GeneralPaperFramedStrategyConstructionStorage.window model W (frame p) (parsed,[]) p.values p.selector p.correct p.budget p.budget_valid cS cD)
      (observed:ℚ)≤(As:ℚ)*spaceScale p*(paperLog p:ℚ)^es ∧ observed<2^W ∧
        GeneralPaperClosedStrategyConstructionStorage.frameReturnedFoot model W (frame p) p.values p.selector p.correct p.budget p.budget_valid<2^W

def FrameContract (model : RationalCostModel) (C d At et As es Ad : ℕ) (p : Problem) : Prop :=
  let W := word model C d p
  ((GeneralPaperClosedStrategyDriver.frame model W W W (GeneralPaperNativeFramedPreparationTime.frame p) p.values p.selector p.correct p.budget p.budget_valid).2:ℚ)≤
    (At:ℚ)*timeScale p*(paperLog p:ℚ)^et ∧ FrameSpace model C d As es p ∧
  ∃ sampler : SamplerFor model C d p,
    (GeneralPaperClosedStrategyDriver.frame model W W W (GeneralPaperNativeFramedPreparationTime.frame p)
      p.values p.selector p.correct p.budget p.budget_valid).1=some (returned model C d p,[]) ∧
    (returned model C d p).sampler=some sampler ∧
    (GeneralPaperClosedDescriptionStorage.footprint W sampler:ℚ)≤(Ad:ℚ)*descriptionScale p*(paperLog p:ℚ)^2 ∧
    (GeneralPaperClosedDescriptionStorage.preparedFoot W (returned model C d p):ℚ)≤(Ad:ℚ)*descriptionScale p*(paperLog p:ℚ)^2 ∧
    Drawing model C d p sampler ∧ Independent model C d p sampler


theorem uniform_frame_contract {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ At et As es Ad : ℕ,∀ p : Problem,epsilon p<1 → FrameContract model C d At et As es Ad p := by
  obtain ⟨At,et,hTime⟩ := GeneralPaperNativeFramedPreparationTime.canonical_frame_time_headline hg
  obtain ⟨As,es,hSpace⟩ := GeneralPaperNativeFramedPreparationTime.canonical_frame_space_headline hg
  obtain ⟨_,_,_,_,Ad,hBit⟩ := uniform_contract hg
  refine ⟨At,et,As,es,Ad,?_⟩
  intro p hOne
  obtain ⟨sampler,hSampler,hFoot,hPrepared,hDraw,hIndependent⟩ := (hBit p hOne).2.2
  exact ⟨hTime p hOne,hSpace p hOne,sampler,
    GeneralPaperNativeReturnedDescriptionHeadline.canonical_frame_return_eq_bit model C d p,
    hSampler,hFoot,hPrepared,hDraw,hIndependent⟩

def RealIndependent {n T K : ℕ} (model : RationalCostModel) (sampler : Sampler n T K) : Prop :=
  let D := sampler.controls.rowBits+sampler.controls.shiftBits
  MeasureTheory.Measure.map (fun fresh =>
    ((fun j => ((run false (fun _ => 1) 1 model sampler false (firstBitBlock D D fresh)).output.read j:ℝ)),
      (fun j => ((run false (fun _ => 1) 1 model sampler true (secondBitBlock D D fresh)).output.read j:ℝ))))
    (fairBitLaw (D+D) : MeasureTheory.Measure (Fin (D+D) → Bool))=
    (law false (fun _ => 1) 1 model sampler false : MeasureTheory.Measure (Allocation n)).prod
      (law false (fun _ => 1) 1 model sampler true : MeasureTheory.Measure (Allocation n))

def RealContract (model : RationalCostModel) (Ar er : ℕ) (p : Problem) : Prop :=
  let actual := (GeneralPaperClosedStrategyDriver.arithmetic model (epsilon p) p.values p.selector p.correct p.budget).1
  ((GeneralPaperClosedStrategyDriver.arithmetic model (epsilon p) p.values p.selector p.correct p.budget).2:ℚ)≤
    (Ar:ℚ)*GeneralPaperRealHeadlineParameters.timeScale p.n (epsilon p)*
      (GeneralPaperRealHeadlineParameters.logarithm p.n (epsilon p):ℚ)^er ∧
  ∃ sampler : Sampler p.n
    (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet actual.raw.strategies.original.reduced.m actual.raw.exponent).lambda actual.raw.exponent).rows
    (GeneralPaperProxyParameters.prepare actual.raw.strategies.original.reduced.m actual.raw.exponent).K,
    actual.sampler=some sampler ∧
    GeneralPaperClosedStrategyEquilibrium.Guarantee false (fun _ => 1) 1 model p.selector.values (p.budget:ℝ) (epsilon p:ℝ) sampler ∧
    (∀ (reciprocal : Bool) (fresh : Fin (sampler.controls.rowBits+sampler.controls.shiftBits) → Bool),
      (run false (fun _ => 1) 1 model sampler reciprocal fresh).work≤131072*(p.n+binaryWordWidth ⌈(epsilon p)⁻¹⌉₊) ∧
      (run false (fun _ => 1) 1 model sampler reciprocal fresh).freshReads=Nat.log2 (sampler.controls.rows*sampler.controls.shifts)) ∧
    RealIndependent model sampler

theorem uniform_real_contract (model : RationalCostModel) :
    ∃ Ar er : ℕ,∀ p : Problem,epsilon p<1 → RealContract model Ar er p := by
  obtain ⟨Ar,er,h⟩ := GeneralPaperClosedArithmeticSampling.headline_with_draws model
  refine ⟨Ar,er,?_⟩
  intro p hOne
  obtain ⟨hTime,sampler,hSampler,hGuarantee,hDraw⟩ := h (epsilon p) (epsilon_positive p) hOne p.values p.selector p.correct p.budget p.budget_valid
  exact ⟨hTime,sampler,hSampler,hGuarantee,hDraw,independent_players false (fun _ => 1) 1 model sampler⟩

end Blotto.GeneralPaperNativeUnequalBudgetContract
