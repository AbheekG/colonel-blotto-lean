import Blotto.GeneralPaperEqualRealMidpoint

/-! Exact-real interpolation/scaling of the small group vector and one
cached coordinate-write pass. Every load, arithmetic primitive, output store,
array advance and route branch has an explicit source-model trace. -/
namespace Blotto.GeneralPaperEqualRealEmission
open scoped BigOperators Classical
open GeneralPaperPositiveSegmentCompaction (compact count)
open GeneralPaperEqualPreparedCache
open PRGRealRAMExecution
set_option autoImplicit false
set_option maxHeartbeats 700000

noncomputable def arrayRunSized {α : Type*} {r : ℕ} (size : ℕ) (hSize : size = r)
    (body : Fin r → Run α) : Run (FixedArrayTable r α) :=
  let actual := arrayRun size (fun i => body (i.cast hSize))
  ⟨⟨actual.value.data, actual.value.size.trans hSize⟩, actual.trace⟩

theorem arrayRunSized_eq {α : Type*} {r : ℕ} (size : ℕ) (hSize : size = r)
    (body : Fin r → Run α) : arrayRunSized size hSize body = arrayRun r body := by
  cases hSize
  rfl

noncomputable def groups {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (slot : Fin (count l)) (t : ℝ) : Run (FixedArrayTable m ℝ) :=
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

theorem groups_data {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool) (g : Fin m) :
    (groups p slot (GeneralPaperEqualPreparedCache.midpoint p fresh : ℝ)).value.read g =
      ((GeneralPaperEqualCachedEmission.scaledPoint p slot fresh).read g : ℝ) := by
  simp only [groups, arrayRunSized_eq, arrayRun_read, arithmetic, Operation.realValue, RealArithmeticOp.apply,
    GeneralPaperEqualCachedEmission.scaledPoint, groupPoint, FixedArrayTable.read_ofFn,
    Rat.cast_mul, Rat.cast_add, Rat.cast_sub, Rat.cast_one]

theorem groups_cost {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (slot : Fin (count l)) (t : ℝ) : (groups p slot t).cost = 8 * m + 6 := by
  unfold groups
  dsimp only
  rw [arrayRunSized_eq]
  change cost _ = _
  simp only [cost_append, cost_cons, cost_nil, Operation.cost, arithmetic]
  change _ + (arrayRun m _).cost = _
  rw [arrayRun_cost]
  simp [Run.cost, Operation.cost]
  ring

noncomputable def coordinate {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (y : FixedArrayTable m ℝ) (j : Fin n) : Run ℝ :=
  match (p.routes.table.read j).1 with
  | none => ⟨0, [.control, .control, .control]⟩
  | some g =>
    let coefficient : Run ℝ := ⟨((p.routes.table.read j).2 : ℝ), [.load j.val ((p.routes.table.read j).2 : ℝ)]⟩
    let sampled := loadReal y g
    let result := arithmetic .mul coefficient.value sampled.value
    ⟨result.value, [.control, .control] ++ coefficient.trace ++ sampled.trace ++ result.trace⟩

noncomputable def output {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (y : FixedArrayTable m ℝ) : Run (FixedArrayTable n ℝ) :=
  arrayRunSized p.routes.table.data.size p.routes.table.size (coordinate p y)

theorem output_data {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (q : Fin m → ℚ) (y : FixedArrayTable m ℝ) (hy : ∀ g, y.read g = (q g : ℝ)) (j : Fin n) :
    (output p y).value.read j = (p.routes.emit q).realAllocation j := by
  rw [output, arrayRunSized_eq, arrayRun_read]
  change (coordinate p y j).value = ((p.routes.emit q).allocation j : ℝ)
  rw [← p.routes.routedValue_eq]
  unfold coordinate PreparedGroupOutput.routedValue
  cases (p.routes.table.read j).1 with
  | none => exact Rat.cast_zero.symm
  | some g => simp only [arithmetic, Operation.realValue, RealArithmeticOp.apply, loadReal, hy g, Rat.cast_mul]

theorem coordinate_cost {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (y : FixedArrayTable m ℝ) (j : Fin n) : (coordinate p y j).cost ≤ 5 := by
  unfold coordinate
  split <;> norm_num [Run.cost, arithmetic, loadReal, Operation.cost]

theorem output_cost {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (y : FixedArrayTable m ℝ) : (output p y).cost ≤ 7 * n + 2 := by
  rw [output, arrayRunSized_eq, arrayRun_cost]
  have hs : (∑ j : Fin n, ((coordinate p y j).cost + 2)) ≤ ∑ _j : Fin n, (7 : ℕ) :=
    Finset.sum_le_sum (fun j _ => Nat.add_le_add_right (coordinate_cost p y j) 2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  exact (Nat.add_le_add_left hs 2).trans_eq (by omega)

end Blotto.GeneralPaperEqualRealEmission
