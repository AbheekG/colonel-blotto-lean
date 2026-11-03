import Blotto.RationalFirstConditionalHeight
import Blotto.RationalLotteryHeight
import Blotto.RationalNestedComponents

/-! Height certificates for actual nested fields, finite locations and
fixed-mean subfamilies. The input domain remains the positive interior domain. -/

namespace Blotto.RationalNestedInput

def FieldsHeight (i : RationalNestedInput) (s : ℕ) : Prop :=
  RationalHeight i.M s ∧ RationalHeight i.a s ∧ RationalHeight i.d s ∧
    RationalHeight i.c s ∧ RationalHeight i.t s ∧ RationalHeight i.q s

theorem FieldsHeight.mono {i : RationalNestedInput} {s t : ℕ}
    (h : i.FieldsHeight s) (hst : s ≤ t) : i.FieldsHeight t :=
  ⟨h.1.mono hst, h.2.1.mono hst, h.2.2.1.mono hst,
    h.2.2.2.1.mono hst, h.2.2.2.2.1.mono hst, h.2.2.2.2.2.mono hst⟩

theorem FieldsHeight.environment {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (x : ℚ) (hx : RationalHeight x s) :
    ∀ j, RationalHeight ((RationalNestedParametersCode.environment i x).read j) s := by
  intro j
  fin_cases j
  · simpa [RationalNestedParametersCode.environment, FixedArrayTable.read_ofFn] using h.1
  · simpa [RationalNestedParametersCode.environment, FixedArrayTable.read_ofFn] using h.2.1
  · simpa [RationalNestedParametersCode.environment, FixedArrayTable.read_ofFn] using h.2.2.1
  · simpa [RationalNestedParametersCode.environment, FixedArrayTable.read_ofFn] using h.2.2.2.1
  · simpa [RationalNestedParametersCode.environment, FixedArrayTable.read_ofFn] using h.2.2.2.2.1
  · simpa [RationalNestedParametersCode.environment, FixedArrayTable.read_ofFn] using h.2.2.2.2.2
  · simpa [RationalNestedParametersCode.environment, FixedArrayTable.read_ofFn] using hx

theorem FieldsHeight.scalar {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (x : ℚ) (hx : RationalHeight x s) (j : Fin 6) :
    RationalHeight (RationalNestedParametersCode.scalarValues i x j) (expressionHeightBudget s 8) :=
  RationalNestedParametersCode.scalar_height i x j s hs (h.environment x hx)

theorem FieldsHeight.firstConditional {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (htv : i.t ≤ i.v) (x : ℚ) (hx : 0 ≤ x ∧ x ≤ i.t)
    (hX : RationalHeight x s) :
    (i.firstConditionalLottery htv x hx).HeightAt (expressionHeightBudget s 19) := by
  constructor
  · intro slot; exact RationalNestedParametersCode.first_weight_height i htv x hx slot s hs (h.environment x hX)
  · intro slot j
    have he := RationalNestedParametersCode.first_endpoint_heights i htv x hx slot j s hs (h.environment x hX)
    have hm := expressionHeightBudget_mono s (by decide : 6 ≤ 19)
    exact ⟨he.1.mono hm, he.2.mono hm⟩

theorem FieldsHeight.midpointLocation {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (bits : Fin K → Bool) :
    RationalHeight (i.midpointLocation K bits) (expressionHeightBudget (max s (K + 2)) 8) := by
  have hFields := h.mono (le_max_left s (K + 2))
  have hMid := (dyadicMidpointSample_height K bits).mono (le_max_right s (K + 2))
  exact hFields.scalar (hs.trans (le_max_left _ _)) _ hMid 0

theorem FieldsHeight.firstMidpoint {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (htv : i.t ≤ i.v) (K : ℕ) (bits : Fin K → Bool) :
    (i.firstConditionalLottery htv (i.midpointLocation K bits) (i.midpointLocation_bounds K bits)).HeightAt
      (expressionHeightBudget (max s (K + 2)) 27) := by
  have hLoc := h.midpointLocation hs K bits
  have hm : s ≤ expressionHeightBudget (max s (K + 2)) 8 :=
    (le_max_left _ _).trans (expressionHeightBudget_ge_input _ _)
  have hTable := (h.mono hm).firstConditional (hs.trans hm) htv _ (i.midpointLocation_bounds K bits) hLoc
  rw [expressionHeightBudget_comp] at hTable
  exact hTable

theorem FieldsHeight.familyInput {i : RationalNestedInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v) (hX : RationalHeight x s) :
    (i.familyInput x hx0 hxv).FieldsHeight (expressionHeightBudget s 8) := by
  have hm := expressionHeightBudget_ge_input s 8
  have hProb : RationalHeight (i.familyProbability x) (expressionHeightBudget s 8) := h.scalar hs x hX 2
  exact ⟨h.1.mono hm, h.2.1.mono hm, h.2.2.1.mono hm,
    h.2.2.2.1.mono hm, hX.mono hm, hProb⟩

end Blotto.RationalNestedInput
