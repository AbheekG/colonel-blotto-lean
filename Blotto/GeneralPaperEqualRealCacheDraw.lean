import Blotto.GeneralPaperEqualRealPreparation

/-! Direct real-model draws from the smaller returned record. No executed
function in this module calls the noncomputable full-cache analysis view.
Equality with that view is used only to transfer the existing law proofs. -/
namespace Blotto.GeneralPaperEqualRealCacheDraw
open MeasureTheory
open scoped BigOperators Classical
open GeneralPaperPositiveSegmentCompaction (count)
open GeneralPaperEqualRealCache (Cache view)
open GeneralPaperEqualRealEmission (arrayRunSized)
open PRGRealRAMExecution
set_option autoImplicit false
set_option maxHeartbeats 1400000

noncomputable def midpoint {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Cache G l) (fresh : Fin p.midpointBits → Bool) : GeneralPaperEqualRealMidpoint.Result :=
  let buffer := GeneralPaperNativeFreshBuffer.run (fun _ => 1) 1 fresh
  let rank := GeneralPaperNativeFairIndex.loop (fun _ => 1) 1 buffer.1.1 0 p.midpointBits
    (by omega) p.midpointBits le_rfl
  let doubled := arithmetic .mul (rank.value : ℝ) 2
  let numerator := arithmetic .add doubled.value 1
  let denominator := arithmetic .mul 2 (p.midpointCount : ℝ)
  let quotient := arithmetic .div numerator.value denominator.value
  ⟨quotient.value, buffer.1.2,
    buffer.2 + rank.work + doubled.cost + numerator.cost + denominator.cost + quotient.cost + 16⟩

noncomputable def groups {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Cache G l) (slot : Fin (count l)) (t : ℝ) : Run (FixedArrayTable m ℝ) :=
  let complement := arithmetic .sub 1 t
  let budget : Run ℝ := ⟨(p.budget : ℝ), [.load 0 (p.budget : ℝ)]⟩
  let cells := arrayRunSized (p.segments.left.read slot).data.size (p.segments.left.read slot).size (fun g =>
    let x : Run ℝ := ⟨((p.segments.left.read slot).read g : ℝ), [.load g.val ((p.segments.left.read slot).read g : ℝ)]⟩
    let y : Run ℝ := ⟨((p.segments.right.read slot).read g : ℝ), [.load g.val ((p.segments.right.read slot).read g : ℝ)]⟩
    let first := arithmetic .mul complement.value x.value
    let second := arithmetic .mul t y.value
    let total := arithmetic .add first.value second.value
    let scaled := arithmetic .mul budget.value total.value
    ⟨scaled.value, x.trace ++ y.trace ++ first.trace ++ second.trace ++ total.trace ++ scaled.trace⟩)
  ⟨cells.value, [.control, .control] ++ complement.trace ++ budget.trace ++ cells.trace⟩

noncomputable def coordinate {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Cache G l) (y : FixedArrayTable m ℝ) (j : Fin n) : Run ℝ :=
  match (p.routes.table.read j).1 with
  | none => ⟨0, [.control, .control, .control]⟩
  | some g =>
    let coefficient : Run ℝ := ⟨((p.routes.table.read j).2 : ℝ), [.load j.val ((p.routes.table.read j).2 : ℝ)]⟩
    let sampled := loadReal y g
    let result := arithmetic .mul coefficient.value sampled.value
    ⟨result.value, [.control, .control] ++ coefficient.trace ++ sampled.trace ++ result.trace⟩

noncomputable def output {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Cache G l) (y : FixedArrayTable m ℝ) : Run (FixedArrayTable n ℝ) :=
  arrayRunSized p.routes.table.data.size p.routes.table.size (coordinate p y)


def weights {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : Cache G l) (i : Fin (count l)) : ℝ := (p.segments.weights.read i : ℝ)

noncomputable def choose {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Cache G l) (u : ℝ) : Run (Fin (count l)) :=
  GeneralPaperRealCumulativeChoice.sizedRun p.segments.weights.data.size p.segments.weights.size
    (weights p) (GeneralPaperPositiveSegmentCompaction.count_positive l) 0 u

noncomputable def run {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Cache G l) (u : ℝ) (fresh : Fin p.midpointBits → Bool) : GeneralPaperEqualRealDraw.Result n :=
  let sampled := uniform u
  let slot := choose p sampled.value
  let scalar := midpoint p fresh
  let groups := groups p slot.value scalar.value
  let written := output p groups.value
  ⟨written.value, 1, scalar.reads,
    sampled.cost + slot.cost + scalar.work + groups.cost + written.cost + 16⟩

theorem run_eq_view {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : Cache G l) (u : ℝ) (fresh : Fin p.midpointBits → Bool) :
    run p u fresh = GeneralPaperEqualRealDraw.run (view p) u fresh := rfl

theorem work {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : Cache G l) (u : ℝ) (fresh : Fin p.midpointBits → Bool) :
    (run p u fresh).work ≤ 5 * count l + 144 * p.midpointBits + 8 * m + 7 * n + 142 := by
  rw [run_eq_view]
  exact GeneralPaperEqualRealDraw.work (view p) u fresh

theorem reads {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : Cache G l) (u : ℝ) (fresh : Fin p.midpointBits → Bool) :
    (run p u fresh).uniformReads = 1 ∧ (run p u fresh).bitReads = p.midpointBits := by
  rw [run_eq_view]
  exact GeneralPaperEqualRealDraw.reads (view p) u fresh

theorem measurable_run {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : Cache G l) : Measurable (fun z : ℝ × (Fin p.midpointBits → Bool) => (run p z.1 z.2).output.read) := by
  simp only [run_eq_view]
  exact GeneralPaperEqualRealDraw.measurable_run (view p)

noncomputable def inputLaw {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : Cache G l) : ProbabilityMeasure (ℝ × (Fin p.midpointBits → Bool)) :=
  ⟨(unitUniform : Measure ℝ).prod (fairBitLaw p.midpointBits : Measure (Fin p.midpointBits → Bool)), inferInstance⟩

noncomputable def outputLaw {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : Cache G l) : Mixed n := (inputLaw p).map (fun z => (run p z.1 z.2).output.read)

theorem outputLaw_eq {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : Cache G l) : outputLaw p = GeneralPaperEqualRealDraw.outputLaw (view p) := by
  unfold outputLaw GeneralPaperEqualRealDraw.outputLaw
  simp only [run_eq_view]
  rfl

theorem independent_players {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : Cache G l) :
    let μ := (inputLaw p : Measure (ℝ × (Fin p.midpointBits → Bool)))
    let f := fun z : ℝ × (Fin p.midpointBits → Bool) => (run p z.1 z.2).output.read
    Measure.map (Prod.map f f) (μ.prod μ) =
      (outputLaw p : Measure (Allocation n)).prod (outputLaw p : Measure (Allocation n)) := by
  dsimp only
  exact (Measure.map_prod_map _ _ (measurable_run p) (measurable_run p)).symm

end Blotto.GeneralPaperEqualRealCacheDraw
