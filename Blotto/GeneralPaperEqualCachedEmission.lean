import Blotto.GeneralPaperEqualPreparedCache
import Blotto.BudgetScalingRegret

/-! A draw writes the whole allocation through cached group routes. The
original common budget is applied to the small sampled group vector before
that coordinate pass. The output ledger includes coordinate arithmetic,
word writes and array/control metadata; drawing/interpolation are separate. -/
namespace Blotto.GeneralPaperEqualCachedEmission
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 700000
open GeneralPaperPositiveSegmentCompaction (compact count)
open GeneralPaperEqualPreparedCache

def scaledPoint {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool) : FixedArrayTable m ℚ :=
  let y := groupPoint p slot fresh
  FixedArrayTable.ofFn (fun g => p.budget * y.read g)

theorem scaledPoint_data {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool) (g : Fin m) :
    (scaledPoint p slot fresh).read g = p.budget * (compact l).point p.midpointBits slot fresh g := by
  simp only [scaledPoint, FixedArrayTable.read_ofFn, groupPoint_data]

def emit {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ)
    (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool) : RationalResourceArray n × ℕ :=
  let y := scaledPoint p slot fresh
  PaperStoredGroupEmission.emit p.routes model primitive A y.read

theorem emit_data {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ)
    (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool) :
    (emit p model primitive A slot fresh).1 = p.routes.emit (scaledPoint p slot fresh).read :=
  PaperStoredGroupEmission.emit_data _ _ _ _ _

theorem emit_real {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ)
    (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool) :
    (emit p model primitive A slot fresh).1.realAllocation =
      scaleAllocation (p.budget : ℝ)
        (G.real.split (fun g => ((compact l).point p.midpointBits slot fresh g : ℝ))) := by
  rw [emit_data, p.routes.emit_real]
  funext j
  simp only [scaledPoint_data, Rat.cast_mul, ProportionalGroups.split, scaleAllocation,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  ring

theorem emit_fullBudget {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ)
    (hb : 0 ≤ p.budget)
    (h : ∀ i, FullBudget 1 (l.real.P i) ∧ FullBudget 1 (l.real.Q i))
    (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool) :
    FullBudget (p.budget : ℝ) (emit p model primitive A slot fresh).1.realAllocation := by
  rw [emit_real]
  have hx := (compact l).point_fullBudget p.midpointBits
    (GeneralPaperPositiveSegmentCompaction.compact_endpoints l 1 h) slot fresh
  have hs := G.real.split_fullBudget hx
  simpa only [mul_one] using scaleAllocation_fullBudget (by exact_mod_cast hb) hs

def groupHeight (s K : ℕ) : ℕ := expressionHeightBudget (max s (K + 2)) 3
def scaledHeight (s K b : ℕ) : ℕ := expressionHeightBudget (max b (groupHeight s K)) 1

theorem groupPoint_height {n m k s : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (hs : 2 ≤ s) (h : l.HeightAt s)
    (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool) (g : Fin m) :
    RationalHeight ((groupPoint p slot fresh).read g) (groupHeight s p.midpointBits) := by
  rw [groupPoint_data]
  exact (GeneralPaperPositiveSegmentCompaction.compact_height l h).point hs _ _ _ _

theorem scaledPoint_height {n m k s b : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (hs : 2 ≤ s) (h : l.HeightAt s) (hB : RationalHeight p.budget b)
    (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool) (g : Fin m) :
    RationalHeight ((scaledPoint p slot fresh).read g) (scaledHeight s p.midpointBits b) := by
  have hx := groupPoint_height p hs h slot fresh g
  have h1 : RationalHeight p.budget (expressionHeightBudget (max b (groupHeight s p.midpointBits)) 0) := by
    simpa only [expressionHeightBudget_zero] using hB.mono (le_max_left _ _)
  have h2 : RationalHeight ((groupPoint p slot fresh).read g)
      (expressionHeightBudget (max b (groupHeight s p.midpointBits)) 0) := by
    simpa only [expressionHeightBudget_zero] using hx.mono (le_max_right _ _)
  simpa only [scaledPoint, FixedArrayTable.read_ofFn, scaledHeight] using h1.mul_level h2

theorem emit_height {n m k s b c : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ)
    (hs : 2 ≤ s) (h : l.HeightAt s) (hB : RationalHeight p.budget b)
    (hc : 1 ≤ c) (hC : ∀ j, RationalHeight (p.routes.table.read j).2 c)
    (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool) (j : Fin n) :
    RationalHeight ((emit p model primitive A slot fresh).1.allocation j)
      (expressionHeightBudget (max c (scaledHeight s p.midpointBits b)) 1) := by
  rw [emit_data]
  exact p.routes.emit_of_coefficient_heights c _ hc hC _ (scaledPoint_height p hs h hB slot fresh) j

theorem emit_work {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ)
    (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool) :
    (emit p model primitive A slot fresh).2 =
      p.routes.emitBitCost model (scaledPoint p slot fresh).read +
      PaperIndexedArrayConstruction.overhead primitive A m m +
      PaperIndexedArrayConstruction.overhead primitive A n n +
      PaperStoredGroupEmission.wrapperWork primitive A n m :=
  PaperStoredGroupEmission.emit_work _ _ _ _ _

theorem emit_work_bound {n m k s b c : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (primitive : ℕ → ℕ) (a : ℕ)
    (hp : ∀ w, primitive w ≤ a * w) (W : ℕ) (hnm : n + m ≤ W)
    (hs : 2 ≤ s) (h : l.HeightAt s) (hB : RationalHeight p.budget b)
    (hc : 2 ≤ c) (hC : ∀ j, RationalHeight (p.routes.table.read j).2 c)
    (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool) :
    (emit p model primitive (StoredArrayReferenceList.poolAddressWidth (n + m + 1) W) slot fresh).2 ≤
      (m + 4 * n) * model.rat (1 + 2 * expressionHeightBudget (max c (scaledHeight s p.midpointBits b)) 1) +
        PaperStoredGroupEmission.metadataBound a n m W := by
  have he := PaperStoredGroupEmission.emit_work_bound p.routes model primitive a hp
    (scaledPoint p slot fresh).read W hnm
  have hr := p.routes.emitBitCost_bound model (scaledPoint p slot fresh).read
    (max c (scaledHeight s p.midpointBits b)) (hc.trans (le_max_left _ _))
    (fun j => (hC j).mono (le_max_left _ _))
    (fun g => (scaledPoint_height p hs h hB slot fresh g).mono (le_max_right _ _))
  exact he.trans (Nat.add_le_add_right hr _)

end Blotto.GeneralPaperEqualCachedEmission
