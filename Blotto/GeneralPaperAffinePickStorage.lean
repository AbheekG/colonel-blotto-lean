import Blotto.GeneralPaperAffineValueStorage

/-! Actual affine minimum pick, including complete input/returned witnesses,
both affine evaluations, comparison scratch and native partial-work fields.
Absent candidates execute no affine arithmetic. -/
namespace Blotto.GeneralPaperAffinePickStorage
open RationalOrderCell GeneralPaperRayAffine GeneralPaperRayAffineMinimum
open GeneralPaperEncodedScalarStorage GeneralPaperAffineWitnessStorage
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def Good {K : ℕ} (n R : ℕ) (a : Option (Choice K)) : Prop :=
  ∀ c,a=some c → c.labels.length≤n ∧ RationalHeight c.expression.intercept R ∧ RationalHeight c.expression.slope R

theorem pick_good {K : ℕ} (model : RationalCostModel) (W n R : ℕ) (t : ℚ) (a b : Option (Choice K))
    (ha : Good n R a) (hb : Good n R b) : Good n R (GeneralPaperAffineMinimumPrice.pickRun model.rat W t a b).1 := by
  intro c hc
  rw [GeneralPaperAffineMinimumPrice.pick_data] at hc
  rcases pick_origin t a b c hc with h|h
  · exact ha c h
  · exact hb c h

def workCap (model : RationalCostModel) (W R s : ℕ) : ℕ := 2*GeneralPaperAffineValueStorage.workCap model W R s+8*W+GeneralPaperAffineValueStorage.price model R s

theorem compare_bound (model : RationalCostModel) (R s : ℕ) (a b : Affine) (t : ℚ)
    (ha : RationalHeight a.intercept R ∧ RationalHeight a.slope R)
    (hb : RationalHeight b.intercept R ∧ RationalHeight b.slope R) (ht : RationalHeight t s) :
    model.rat (RationalExpression.pairWidth (a.value t) (b.value t))≤GeneralPaperAffineValueStorage.price model R s :=
  model.monotone (max_le
    (rationalWordWidth_of_height (GeneralPaperAffineValueStorage.operands R s a t ha.1 ha.2 ht).2.2)
    (rationalWordWidth_of_height (GeneralPaperAffineValueStorage.operands R s b t hb.1 hb.2 ht).2.2))

theorem work {K : ℕ} (model : RationalCostModel) (W n R s : ℕ) (t : ℚ) (ht : RationalHeight t s)
    (a b : Option (Choice K)) (ha : Good n R a) (hb : Good n R b) :
    (GeneralPaperAffineMinimumPrice.pickRun model.rat W t a b).2≤workCap model W R s := by
  cases a with
  | none => simp only [GeneralPaperAffineMinimumPrice.pickRun]; unfold workCap; omega
  | some a =>
    cases b with
    | none => simp only [GeneralPaperAffineMinimumPrice.pickRun]; unfold workCap; omega
    | some b =>
      have hA := ha a rfl
      have hB := hb b rfl
      have hFirst := GeneralPaperAffineValueStorage.work model W R s a.expression t hA.2.1 hA.2.2 ht
      have hSecond := GeneralPaperAffineValueStorage.work model W R s b.expression t hB.2.1 hB.2.2 ht
      have hCompare := compare_bound model R s a.expression b.expression t hA.2 hB.2 ht
      change (GeneralPaperAffineValuePrice.run model.rat W a.expression t).2+
        (GeneralPaperAffineValuePrice.run model.rat W b.expression t).2+8*W+
          model.rat (RationalExpression.pairWidth (a.expression.value t) (b.expression.value t))≤_
      unfold workCap
      omega

def arithmetic {K : ℕ} (model : RationalCostModel) (W : ℕ) (t : ℚ) : Option (Choice K) → Option (Choice K) → ℕ
  | some a,some b =>
    let first := GeneralPaperAffineValuePrice.run model.rat W a.expression t
    let second := GeneralPaperAffineValuePrice.run model.rat W b.expression t
    let compare := model.rat (RationalExpression.pairWidth first.1 second.1)
    GeneralPaperAffineValueStorage.window model W a.expression t+GeneralPaperAffineValueStorage.window model W b.expression t+compare+
      fields W [first.2,second.2,compare,first.2+second.2,first.2+second.2+8*W,
        (GeneralPaperAffineMinimumPrice.pickRun model.rat W t (some a) (some b)).2]+128*W
  | _,_ => 0

def arithmeticProfile (model : RationalCostModel) (W R s : ℕ) : ℕ :=
  2*GeneralPaperAffineValueStorage.profile model W R s+GeneralPaperAffineValueStorage.price model R s+
    6*(natBits (1+workCap model W R s)+W)+160*W

theorem arithmetic_bound {K : ℕ} (model : RationalCostModel) (W n R s : ℕ) (t : ℚ) (ht : RationalHeight t s)
    (a b : Option (Choice K)) (ha : Good n R a) (hb : Good n R b) :
    arithmetic model W t a b≤arithmeticProfile model W R s := by
  cases a with
  | none => simp only [arithmetic]; omega
  | some a =>
    cases b with
    | none => simp only [arithmetic]; omega
    | some b =>
      let first := GeneralPaperAffineValuePrice.run model.rat W a.expression t
      let second := GeneralPaperAffineValuePrice.run model.rat W b.expression t
      let compare := model.rat (RationalExpression.pairWidth first.1 second.1)
      let selected := GeneralPaperAffineMinimumPrice.pickRun model.rat W t (some a) (some b)
      have hA := ha a rfl
      have hB := hb b rfl
      have hFirst := GeneralPaperAffineValueStorage.bounded model W R s a.expression t hA.2.1 hA.2.2 ht
      have hSecond := GeneralPaperAffineValueStorage.bounded model W R s b.expression t hB.2.1 hB.2.2 ht
      have hWork := work model W n R s t ht (some a) (some b) ha hb
      change selected.2≤workCap model W R s at hWork
      have hCompare := compare_bound model R s a.expression b.expression t hA.2 hB.2 ht
      change compare≤GeneralPaperAffineValueStorage.price model R s at hCompare
      have hShape : selected.2=first.2+second.2+8*W+compare := rfl
      have hf := fields_bound W (natBits (1+workCap model W R s))
        [first.2,second.2,compare,first.2+second.2,first.2+second.2+8*W,selected.2] (by
          intro a ha
          apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
          simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
      change GeneralPaperEncodedScalarStorage.fields W _≤6*(natBits (1+workCap model W R s)+W)+32*W at hf
      change GeneralPaperAffineValueStorage.window model W a.expression t+GeneralPaperAffineValueStorage.window model W b.expression t+compare+
        GeneralPaperEncodedScalarStorage.fields W [first.2,second.2,compare,first.2+second.2,first.2+second.2+8*W,selected.2]+128*W≤_
      unfold arithmeticProfile
      omega

def window {K : ℕ} (model : RationalCostModel) (W : ℕ) (t : ℚ) (a b : Option (Choice K)) : ℕ :=
  let result := GeneralPaperAffineMinimumPrice.pickRun model.rat W t a b
  optionChoiceFoot W a+optionChoiceFoot W b+optionChoiceFoot W result.1+rationalWordWidth t+
    fields W [result.2,8*W]+128*W+arithmetic model W t a b

def profile (model : RationalCostModel) (W K n R s : ℕ) : ℕ :=
  3*optionChoiceProfile W K n R+(1+2*s)+2*(natBits (1+workCap model W R s)+W)+160*W+
    arithmeticProfile model W R s

theorem bounded {K : ℕ} (model : RationalCostModel) (W n R s : ℕ) (t : ℚ) (ht : RationalHeight t s)
    (a b : Option (Choice K)) (ha : Good n R a) (hb : Good n R b) :
    window model W t a b≤profile model W K n R s := by
  let result := GeneralPaperAffineMinimumPrice.pickRun model.rat W t a b
  have hA := option_choice_bound W n R a ha
  have hB := option_choice_bound W n R b hb
  have hResult := option_choice_bound W n R result.1 (pick_good model W n R t a b ha hb)
  have hT := rationalWordWidth_of_height ht
  have hWork := work model W n R s t ht a b ha hb
  change result.2≤workCap model W R s at hWork
  have hEight : 8*W≤workCap model W R s := by unfold workCap; omega
  have hf := fields_bound W (natBits (1+workCap model W R s)) [result.2,8*W] (by
    intro a ha
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl <;> omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤2*(natBits (1+workCap model W R s)+W)+32*W at hf
  have hArithmetic := arithmetic_bound model W n R s t ht a b ha hb
  change optionChoiceFoot W a+optionChoiceFoot W b+optionChoiceFoot W result.1+rationalWordWidth t+
    GeneralPaperEncodedScalarStorage.fields W [result.2,8*W]+128*W+arithmetic model W t a b≤_
  unfold profile
  omega

end Blotto.GeneralPaperAffinePickStorage
