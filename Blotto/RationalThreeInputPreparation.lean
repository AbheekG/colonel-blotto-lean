import Blotto.RationalPreparedDescriptorCost

/-! The actual ordered three-input compiler prices its numerical regime
guard, four derived geometry fields and complete compiled descriptor, including
the exceptional branch. Environment setup, caller repetition and backend costs
remain separate from these per-construction formula/data components. -/

namespace Blotto.RationalThreeInputCode
open scoped BigOperators

def regime : Expr := .sub (.add A D) B

theorem regime_value (i : RationalThreeInput) : regime.value (environment i) = i.a + i.d - i.B := by
  simp [regime, A, D, B, environment, FixedArrayTable.read_ofFn]

theorem regime_intermediates (i : RationalThreeInput) (s : ℕ)
    (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    regime.AllRunHeights (environment i) (expressionHeightBudget s 2) := by
  have hLit : regime.LiteralHeights s := by simp [regime, A, D, B, RationalExpression.LiteralHeights]
  have h := regime.run_all_heights _ s hEnv hLit
  have hd : regime.depth = 2 := by decide
  simpa only [hd] using h

theorem regime_height (i : RationalThreeInput) (s : ℕ)
    (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    RationalHeight (i.a + i.d - i.B) (expressionHeightBudget s 2) := by
  have hLit : regime.LiteralHeights s := by simp [regime, A, D, B, RationalExpression.LiteralHeights]
  have h := regime.run_height _ s hEnv hLit
  change RationalHeight (regime.value (environment i)) (expressionHeightBudget s regime.depth) at h
  have hd : regime.depth = 2 := by decide
  rw [regime_value, hd] at h
  exact h

def regimeBitCost (model : RationalCostModel) (i : RationalThreeInput) : ℕ :=
  regime.bitCost model (environment i) + rationalWordWidth (0 : ℚ) + rationalWordWidth (i.a + i.d - i.B) +
    model.rat (RationalExpression.pairWidth 0 (i.a + i.d - i.B))

theorem regimeBitCost_bound (model : RationalCostModel) (i : RationalThreeInput) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    regimeBitCost model i ≤ 8 * model.rat (1 + 2 * expressionHeightBudget s 2) := by
  let W := 1 + 2 * expressionHeightBudget s 2
  have hc := regime.bitCost_bound model _ _ (regime_intermediates i s hEnv)
  have ho : regime.operationBound = 5 := by decide
  rw [ho] at hc
  have hValue := regime_height i s hEnv
  have hZero : RationalHeight (0 : ℚ) (expressionHeightBudget s 2) :=
    (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono (hs.trans (expressionHeightBudget_ge_input s 2))
  have hv := (rationalWordWidth_of_height hValue).trans (model.word_le W)
  have hz := (rationalWordWidth_of_height hZero).trans (model.word_le W)
  have hp := model.monotone (RationalExpression.pairWidth_height hZero hValue)
  change regime.bitCost model (environment i) ≤ 5 * model.rat W at hc
  change model.rat (RationalExpression.pairWidth 0 (i.a + i.d - i.B)) ≤ model.rat W at hp
  change regimeBitCost model i ≤ 8 * model.rat W
  unfold regimeBitCost
  omega

def parameterFieldBitCost (model : RationalCostModel) (i : RationalThreeInput) : ℕ :=
  ∑ j : Fin 4, ((parameters j).bitCost model (environment i) + rationalWordWidth ((parameters j).value (environment i)))

theorem parameterFieldBitCost_bound (model : RationalCostModel) (i : RationalThreeInput) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    parameterFieldBitCost model i ≤ 36 * model.rat (1 + 2 * expressionHeightBudget s 2) := by
  have hp : ∀ j : Fin 4, (parameters j).bitCost model (environment i) + rationalWordWidth ((parameters j).value (environment i)) ≤
      9 * model.rat (1 + 2 * expressionHeightBudget s 2) := by
    intro j
    have hLit := (parameters j).LiteralHeights_mono hs (parameter_literals j)
    have hm := expressionHeightBudget_mono s (parameter_depth j)
    have hAll := (parameters j).run_all_heights _ s hEnv hLit
    have hc := ((parameters j).bitCost_bound model _ _ (RationalExpression.AllRunHeights_mono _ _ hm hAll)).trans
      (Nat.mul_le_mul_right _ (parameter_operations j))
    have hValue := ((parameters j).run_height _ s hEnv hLit).mono hm
    change RationalHeight ((parameters j).value (environment i)) (expressionHeightBudget s 2) at hValue
    have hw := (rationalWordWidth_of_height hValue).trans (model.word_le _)
    omega
  calc
    _ ≤ ∑ _j : Fin 4, 9 * model.rat (1 + 2 * expressionHeightBudget s 2) := Finset.sum_le_sum (fun j _ => hp j)
    _ = _ := by simp; ring

theorem descriptor_height (i : RationalThreeInput) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    i.segmentLottery.HeightAt (expressionHeightBudget s 18) := by
  constructor
  · intro slot; exact segment_weight_height i slot s hs hEnv
  · intro slot j
    have h := segment_endpoint_heights i slot j s hs hEnv
    have hm := expressionHeightBudget_mono s (by decide : 4 ≤ 18)
    exact ⟨h.1.mono hm, h.2.mono hm⟩

noncomputable def preparedInputBitCost (model : RationalCostModel) (i : RationalThreeInput) : ℕ :=
  regimeBitCost model i + if hE : 0 < i.a + i.d - i.B then
    parameterFieldBitCost model i + RationalThreeGeometryCode.preparedDescriptorBitCost model (i.geometry hE)
  else (PreparedSegmentDescriptor.prepare i.segmentLottery).payloadBitCost

theorem preparedInputBitCost_bound (model : RationalCostModel) (i : RationalThreeInput) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    preparedInputBitCost model i ≤ 2843 * model.rat (1 + 2 * expressionHeightBudget s 18) := by
  let W := 1 + 2 * expressionHeightBudget s 18
  have hm := model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (expressionHeightBudget_mono s (by decide : 2 ≤ 18))) 1)
  have hGuard := (regimeBitCost_bound model i s hs hEnv).trans (Nat.mul_le_mul_left 8 hm)
  change regimeBitCost model i ≤ 8 * model.rat W at hGuard
  unfold preparedInputBitCost
  split
  · rename_i hE
    have hFields := (parameterFieldBitCost_bound model i s hs hEnv).trans (Nat.mul_le_mul_left 36 hm)
    have hDesc := RationalThreeGeometryCode.preparedDescriptorBitCost_bound model (i.geometry hE) _
      (hs.trans (expressionHeightBudget_ge_input s 2)) (geometry_environment_height i hE s hs hEnv)
    rw [expressionHeightBudget_comp] at hDesc
    change parameterFieldBitCost model i ≤ 36 * model.rat W at hFields
    change RationalThreeGeometryCode.preparedDescriptorBitCost model (i.geometry hE) ≤ 2799 * model.rat W at hDesc
    change regimeBitCost model i + (parameterFieldBitCost model i +
      RationalThreeGeometryCode.preparedDescriptorBitCost model (i.geometry hE)) ≤ 2843 * model.rat W
    omega
  · have hPayload := (PreparedSegmentDescriptor.prepare i.segmentLottery).payloadBitCost_bound _ (descriptor_height i s hs hEnv)
    have hCopies := hPayload.trans (Nat.mul_le_mul_left 63 (model.word_le W))
    change regimeBitCost model i + (PreparedSegmentDescriptor.prepare i.segmentLottery).payloadBitCost ≤ 2843 * model.rat W
    omega

end Blotto.RationalThreeInputCode
