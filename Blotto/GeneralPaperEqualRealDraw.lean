import Blotto.GeneralPaperEqualRealEmission
import Blotto.GeneralPaperRealCumulativeProductLaw

/-! Complete bounded real-model draw from the compact cache: one real
uniform categorical input, one K-bit midpoint block, small-group interpolation
and budget scaling, and the full cached coordinate-write pass. -/
namespace Blotto.GeneralPaperEqualRealDraw
open MeasureTheory
open scoped BigOperators Classical
open GeneralPaperPositiveSegmentCompaction (compact count)
open GeneralPaperEqualPreparedCache (Prepared)
open PRGRealRAMExecution
set_option autoImplicit false
set_option maxHeartbeats 700000

def weights {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (i : Fin (count l)) : ℝ := (p.segments.weights.read i : ℝ)

theorem weights_nonnegative {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (i : Fin (count l)) : 0 ≤ weights p i := p.segments.lottery.real.nonnegative i

theorem weights_mass {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) : ∑ i, weights p i = 1 := p.segments.lottery.real.mass

noncomputable def choose {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (u : ℝ) : Run (Fin (count l)) :=
  GeneralPaperRealCumulativeChoice.sizedRun p.segments.weights.data.size p.segments.weights.size
    (weights p) (GeneralPaperPositiveSegmentCompaction.count_positive l) 0 u

theorem choose_eq {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (u : ℝ) : choose p u = GeneralPaperRealCumulativeChoice.manyRun
      (weights p) (GeneralPaperPositiveSegmentCompaction.count_positive l) 0 u :=
  GeneralPaperRealCumulativeChoice.sizedRun_eq _ _ _ _ _ _

noncomputable def point {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (i : Fin (count l)) (fresh : Fin p.midpointBits → Bool) : Allocation n :=
  (p.routes.emit (GeneralPaperEqualCachedEmission.scaledPoint p i fresh).read).realAllocation

theorem point_eq_emit {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ)
    (i : Fin (count l)) (fresh : Fin p.midpointBits → Bool) :
    point p i fresh = (GeneralPaperEqualCachedEmission.emit p model primitive A i fresh).1.realAllocation := by
  rw [GeneralPaperEqualCachedEmission.emit_data]
  rfl

structure Result (n : ℕ) where
  output : FixedArrayTable n ℝ
  uniformReads : ℕ
  bitReads : ℕ
  work : ℕ

noncomputable def run {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (u : ℝ) (fresh : Fin p.midpointBits → Bool) : Result n :=
  let sampled := uniform u
  let slot := choose p sampled.value
  let scalar := GeneralPaperEqualRealMidpoint.run p fresh
  let groups := GeneralPaperEqualRealEmission.groups p slot.value scalar.value
  let written := GeneralPaperEqualRealEmission.output p groups.value
  ⟨written.value, 1, scalar.reads,
    sampled.cost + slot.cost + scalar.work + groups.cost + written.cost + 16⟩

theorem data {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (u : ℝ) (fresh : Fin p.midpointBits → Bool) :
    (run p u fresh).output.read = point p (choose p u).value fresh := by
  funext j
  unfold run
  dsimp only
  apply GeneralPaperEqualRealEmission.output_data
  intro g
  rw [GeneralPaperEqualRealMidpoint.data]
  exact GeneralPaperEqualRealEmission.groups_data p _ fresh g

theorem reads {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (u : ℝ) (fresh : Fin p.midpointBits → Bool) :
    (run p u fresh).uniformReads = 1 ∧ (run p u fresh).bitReads = p.midpointBits :=
  ⟨rfl, GeneralPaperEqualRealMidpoint.reads p fresh⟩

theorem work {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (u : ℝ) (fresh : Fin p.midpointBits → Bool) :
    (run p u fresh).work ≤ 5 * count l + 144 * p.midpointBits + 8 * m + 7 * n + 142 := by
  have hc := GeneralPaperRealCumulativeChoice.manyRun_cost (weights p)
    (GeneralPaperPositiveSegmentCompaction.count_positive l) 0 u
  have hm := GeneralPaperEqualRealMidpoint.work p fresh
  have hg := GeneralPaperEqualRealEmission.groups_cost p (choose p u).value (GeneralPaperEqualRealMidpoint.run p fresh).value
  have ho := GeneralPaperEqualRealEmission.output_cost p
    (GeneralPaperEqualRealEmission.groups p (choose p u).value (GeneralPaperEqualRealMidpoint.run p fresh).value).value
  rw [← choose_eq] at hc
  change 1 + (choose p u).cost + (GeneralPaperEqualRealMidpoint.run p fresh).work +
    (GeneralPaperEqualRealEmission.groups p (choose p u).value (GeneralPaperEqualRealMidpoint.run p fresh).value).cost +
    (GeneralPaperEqualRealEmission.output p
      (GeneralPaperEqualRealEmission.groups p (choose p u).value (GeneralPaperEqualRealMidpoint.run p fresh).value).value).cost + 16 ≤ _
  omega

theorem measurable_run {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) : Measurable (fun z : ℝ × (Fin p.midpointBits → Bool) => (run p z.1 z.2).output.read) := by
  have hc := GeneralPaperRealCumulativeChoice.manyRun_measurable (weights p)
    (GeneralPaperPositiveSegmentCompaction.count_positive l) 0
  have hf : Measurable ((fun z : Fin (count l) × (Fin p.midpointBits → Bool) => point p z.1 z.2) :
      (Fin (count l) × (Fin p.midpointBits → Bool)) → (Fin n → ℝ)) :=
    measurable_of_countable _
  have hc' : Measurable (fun u => (choose p u).value) := by simpa only [choose_eq] using hc
  have he : (fun z : ℝ × (Fin p.midpointBits → Bool) => (run p z.1 z.2).output.read) =
      fun z => point p (choose p z.1).value z.2 := funext (fun z => data p z.1 z.2)
  rw [he]
  have hfirst : Measurable (fun z : ℝ × (Fin p.midpointBits → Bool) => (choose p z.1).value) := hc'.comp measurable_fst
  have hpair : Measurable (fun z : ℝ × (Fin p.midpointBits → Bool) => ((choose p z.1).value, z.2)) :=
    hfirst.prodMk measurable_snd
  simpa only [Function.comp_def] using hf.comp hpair

noncomputable def inputLaw {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) : ProbabilityMeasure (ℝ × (Fin p.midpointBits → Bool)) :=
  ⟨(unitUniform : Measure ℝ).prod (fairBitLaw p.midpointBits : Measure (Fin p.midpointBits → Bool)), inferInstance⟩

noncomputable def outputLaw {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) : Mixed n := (inputLaw p).map (fun z => (run p z.1 z.2).output.read)

noncomputable def slotLaw {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) : Mixed n :=
  probabilityMixture (weights p) (fun i => (fairBitLaw p.midpointBits).map (point p i))
    (weights_nonnegative p) (weights_mass p)

theorem outputLaw_slotLaw {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) : outputLaw p = slotLaw p := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun z => (run p z.1 z.2).output.read)
    ((unitUniform : Measure ℝ).prod (fairBitLaw p.midpointBits : Measure (Fin p.midpointBits → Bool))) = _
  simp only [data, choose_eq]
  exact GeneralPaperRealCumulativeChoice.product_law (weights p)
    (GeneralPaperPositiveSegmentCompaction.count_positive l) (weights_nonnegative p) (weights_mass p) 0
    (fairBitLaw p.midpointBits : Measure (Fin p.midpointBits → Bool))
    (fun z => point p z.1 z.2) (measurable_of_countable _)

theorem slotLaw_target {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) : slotLaw p = GeneralPaperEqualCachedTraceLaw.target p := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro S hS
  have hReal : (slotLaw p : Measure (Allocation n)).real S = (GeneralPaperEqualCachedTraceLaw.target p : Measure (Allocation n)).real S := by
    rw [slotLaw, probabilityMixture_real_apply _ _ _ _ _ hS,
      GeneralPaperEqualCachedTraceLaw.target_event p RationalCostModel.schoolbook (fun _ => 1) 1 S hS]
    apply Finset.sum_congr rfl
    intro i _
    rw [weights, p.segments.weight_correct]
    congr 1
    change (Measure.map (point p i) (fairBitLaw p.midpointBits : Measure (Fin p.midpointBits → Bool))).real S = _
    rw [map_measureReal_apply (measurable_of_countable _) hS, GeneralPaperEqualRejectionAllocation.fair_event]
    apply congrArg (fairBitKernel p.midpointBits).mean
    funext fresh
    rw [← point_eq_emit p RationalCostModel.schoolbook (fun _ => 1) 1 i fresh]
    rfl
  have he := congrArg ENNReal.ofReal hReal
  rw [ofReal_measureReal (measure_ne_top _ _), ofReal_measureReal (measure_ne_top _ _)] at he
  exact he

theorem outputLaw_eq {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) : outputLaw p = GeneralPaperEqualCachedTraceLaw.target p := by
  rw [outputLaw_slotLaw, slotLaw_target]

end Blotto.GeneralPaperEqualRealDraw
