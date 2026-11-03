import Blotto.RealCategoricalReference
import Blotto.RealSegmentFlat
import Blotto.RealExpression
import Blotto.RealThreeInputPreparation
import Blotto.RealThreeSampler

/-! An explicit exact-real RAM execution prerequisite. Named arithmetic and
comparisons have unit cost; finite addresses, loads/stores and control actions
have unit cost. Exact independent uniform inputs are unit-cost model primitives.
The interpreter returns data produced by those operations and its selected trace.
This is not a Lean-host, IEEE, LLVM, allocator or bit-machine cost theorem.

The complete stored segment-table draw below includes table traversal, one mass
sum, every reached categorical branch and one selected row interpolation. It
preserves the original complete allocation/law and prices control/address work
without a supplied count oracle. The global PRG preparation/terminal-factory
join remains a separate prerequisite: existing RealNestedFormulaWork explicitly
excludes native constructors and control and cannot substitute for its execution.
-/
namespace Blotto.PRGRealRAMExecution
open MeasureTheory
open scoped BigOperators Classical

inductive Operation where
  | arithmetic (op : RealArithmeticOp) (first second : ℝ)
  | comparison (first second : ℝ)
  | strictComparison (first second : ℝ)
  | load (address : ℕ) (value : ℝ)
  | store (address : ℕ) (value : ℝ)
  | storeCell (address : ℕ)
  | uniform (value : ℝ)
  | control

/-- Min/max expand into a comparison followed by a selection. -/
def Operation.cost : Operation → ℕ
  | .arithmetic .minimum _ _ | .arithmetic .maximum _ _ => 2
  | _ => 1

noncomputable def Operation.realValue : Operation → ℝ
  | .arithmetic op x y => op.apply x y
  | .load _ value | .store _ value | .uniform value => value
  | .comparison x y => if x ≤ y then 1 else 0
  | .strictComparison x y => if x < y then 1 else 0
  | .control | .storeCell _ => 0

structure Run (α : Type*) where
  value : α
  trace : List Operation

def Run.cost {α : Type*} (run : Run α) : ℕ := (run.trace.map Operation.cost).sum

def cost (trace : List Operation) : ℕ := (trace.map Operation.cost).sum

@[simp] theorem cost_nil : cost [] = 0 := rfl
@[simp] theorem cost_append (a b : List Operation) : cost (a ++ b) = cost a + cost b := by
  simp [cost,List.map_append,List.sum_append]

@[simp] theorem cost_cons (op : Operation) (rest : List Operation) : cost (op :: rest) = op.cost + cost rest := rfl

noncomputable def arithmetic (op : RealArithmeticOp) (x y : ℝ) : Run ℝ :=
  ⟨(Operation.arithmetic op x y).realValue,[.arithmetic op x y]⟩

noncomputable def loadReal {n : ℕ} (table : FixedArrayTable n ℝ) (j : Fin n) : Run ℝ :=
  ⟨(Operation.load j.val (table.read j)).realValue,[.load j.val (table.read j)]⟩

noncomputable def uniform (x : ℝ) : Run ℝ :=
  ⟨(Operation.uniform x).realValue,[.uniform x]⟩

noncomputable def compareLe (x y : ℝ) : Run Bool :=
  ⟨decide (x ≤ y),[.comparison x y]⟩

/-- A RAM for-loop evaluates each body once, stores each result once and prices
its control/advance action. The trace is interpretation data, not host logging. -/
noncomputable def arrayRun {α : Type*} (n : ℕ) (body : Fin n → Run α) : Run (FixedArrayTable n α) :=
  let cells := FixedArrayTable.ofFn body
  ⟨FixedArrayTable.ofFn (fun j => (cells.read j).value),
    [.control] ++ (List.ofFn fun j => (cells.read j).trace ++ [.storeCell j.val,.control]).flatten ++ [.control]⟩

@[simp] theorem arrayRun_read {α : Type*} (n : ℕ) (body : Fin n → Run α) (j : Fin n) :
    (arrayRun n body).value.read j = (body j).value := by
  simp [arrayRun,FixedArrayTable.read_ofFn]

 theorem cost_flatten (traces : List (List Operation)) :
    cost traces.flatten = (traces.map cost).sum := by
  induction traces with
  | nil => rfl
  | cons trace rest ih => simp [ih]

 theorem arrayRun_cost {α : Type*} (n : ℕ) (body : Fin n → Run α) :
    (arrayRun n body).cost = 2 + ∑ j, ((body j).cost + 2) := by
  unfold arrayRun Run.cost
  change cost ([.control] ++ (List.ofFn _).flatten ++ [.control]) = _
  simp only [cost_append,cost_flatten,List.map_ofFn,List.sum_ofFn,FixedArrayTable.read_ofFn,
    cost_cons,cost_nil,Operation.cost]
  simp only [Function.comp_def,cost_append,cost_cons,cost_nil,Operation.cost]
  simp only [cost,Nat.reduceAdd,Nat.add_zero]
  omega

noncomputable def binary (op : RealArithmeticOp) (x y : Run ℝ) : Run ℝ :=
  let result := arithmetic op x.value y.value
  ⟨result.value,x.trace ++ y.trace ++ result.trace⟩

/-- Every arithmetic expression is evaluated through named primitives; only
one conditional arm is interpreted. -/
noncomputable def expression {k : ℕ} (env : FixedArrayTable k ℝ) : RationalExpression k → Run ℝ
  | .input j => loadReal env j
  | .literal q => ⟨q,[.load 0 q]⟩
  | .add a b => binary .add (expression env a) (expression env b)
  | .sub a b => binary .sub (expression env a) (expression env b)
  | .mul a b => binary .mul (expression env a) (expression env b)
  | .div a b => binary .div (expression env a) (expression env b)
  | .minimum a b => binary .minimum (expression env a) (expression env b)
  | .maximum a b => binary .maximum (expression env a) (expression env b)
  | .ifLe a b yes no =>
      let x := expression env a
      let y := expression env b
      let compared := compareLe x.value y.value
      let result := if compared.value then expression env yes else expression env no
      ⟨result.value,x.trace ++ y.trace ++ compared.trace ++ result.trace⟩

@[simp] theorem expression_value {k : ℕ} (env : FixedArrayTable k ℝ) (e : RationalExpression k) :
    (expression env e).value = e.realValue env := by
  induction e with
  | input j => rfl
  | literal q => rfl
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      simp only [expression,binary,arithmetic,Operation.realValue,RealArithmeticOp.apply,
        ha,hb,RationalExpression.realValue_add,RationalExpression.realValue_sub,
        RationalExpression.realValue_mul,RationalExpression.realValue_div,
        RationalExpression.realValue_minimum,RationalExpression.realValue_maximum]
  | ifLe a b yes no ha hb hy hn =>
      simp only [expression,compareLe,ha,hb]
      simp only [decide_eq_true_eq,RationalExpression.realValue_ifLe]
      by_cases h : a.realValue env ≤ b.realValue env
      · simp only [h,ite_true,hy]
      · simp only [h,ite_false,hn]

 theorem binary_cost (op : RealArithmeticOp) (x y : Run ℝ) :
    (binary op x y).cost ≤ x.cost + y.cost + 2 := by
  unfold binary Run.cost arithmetic
  change cost (x.trace ++ y.trace ++ [.arithmetic op x.value y.value]) ≤ _
  simp only [cost_append,cost_cons,cost_nil]
  cases op <;> simp [Operation.cost,cost]

 theorem expression_cost {k : ℕ} (env : FixedArrayTable k ℝ) (e : RationalExpression k) :
    (expression env e).cost ≤ 2 * e.operationBound := by
  induction e with
  | input j | literal q => simp [expression,loadReal,Run.cost,Operation.cost,RationalExpression.operationBound]
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      simp only [expression,RationalExpression.operationBound]
      apply (binary_cost _ _ _).trans
      omega
  | ifLe a b yes no ha hb hy hn =>
      have hY := le_max_left yes.operationBound no.operationBound
      have hN := le_max_right yes.operationBound no.operationBound
      unfold expression
      dsimp only
      unfold Run.cost at *
      split <;> simp only [List.map_append,List.sum_append,compareLe,
        List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Operation.cost,
        RationalExpression.operationBound] <;> omega

/-- The input consists of stored tables. Constructing these tables from a
three/nested/four factory is not charged as a primitive read. -/
structure PreparedSegment (n k : ℕ) where
  weight : FixedArrayTable k ℝ
  P : FixedArrayTable k (FixedArrayTable n ℝ)
  Q : FixedArrayTable k (FixedArrayTable n ℝ)

noncomputable def PreparedSegment.ofLottery {n k : ℕ} (l : SegmentLottery n k) : PreparedSegment n k :=
  ⟨FixedArrayTable.ofFn l.weight,FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (l.P slot)),
    FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn (l.Q slot))⟩

noncomputable def weightList {k : ℕ} (table : FixedArrayTable k ℝ) : Run (List (Fin k × ℝ)) :=
  ⟨List.ofFn (fun j => (j,(loadReal table j).value)),
    (List.ofFn (fun j => (loadReal table j).trace ++ [.control,.control])).flatten ++ [.control]⟩

 theorem weightList_value {k : ℕ} (table : FixedArrayTable k ℝ) :
    (weightList table).value = List.ofFn (fun j => (j,table.read j)) := rfl

 theorem weightList_cost {k : ℕ} (table : FixedArrayTable k ℝ) : (weightList table).cost = 3 * k + 1 := by
  unfold weightList Run.cost
  change cost ((List.ofFn _).flatten ++ [.control]) = _
  simp only [cost_append,cost_flatten,List.map_ofFn,List.sum_ofFn,loadReal,cost_cons,cost_nil,
    Operation.cost]
  simp [cost,Operation.cost,Nat.mul_comm]

noncomputable def sumWeights : List ℝ → Run ℝ
  | [] => ⟨0,[.control]⟩
  | x :: rest =>
      let later := sumWeights rest
      let result := arithmetic .add x later.value
      ⟨result.value,.control :: (later.trace ++ result.trace)⟩

 theorem sumWeights_value (values : List ℝ) : (sumWeights values).value = values.sum := by
  induction values with
  | nil => rfl
  | cons x xs ih => simp [sumWeights,arithmetic,Operation.realValue,RealArithmeticOp.apply,ih]

 theorem sumWeights_cost (values : List ℝ) : (sumWeights values).cost = 2 * values.length + 1 := by
  induction values with
  | nil => rfl
  | cons x xs ih =>
      unfold sumWeights Run.cost
      change cost (.control :: ((sumWeights xs).trace ++ [.arithmetic .add x (sumWeights xs).value])) = _
      simp only [cost_cons,cost_append,cost_nil,Operation.cost]
      change 1 + ((sumWeights xs).cost + 1) = _
      rw [ih]
      simp only [List.length_cons]
      omega

/-- Complete selected categorical execution. Mass is computed once by the
caller; each lower continuation computes one subtraction, not a suffix sum. -/
noncomputable def categorical {α : Type*} (fallback : α) :
    (C : ℕ) → List (α × ℝ) → ℝ → (Fin C → ℝ) → Run α
  | _, [], _, _ => ⟨fallback,[.control]⟩
  | _, [head], _, _ => ⟨head.1,[.control,.control]⟩
  | 0, head :: _ :: _, mass, _ =>
      if 0 < mass then ⟨fallback,[.control,.strictComparison 0 mass,.control]⟩
      else ⟨head.1,[.control,.strictComparison 0 mass,.control]⟩
  | C + 1, head :: next :: tail, mass, seed =>
      if 0 < mass then
        let nextMass := arithmetic .sub mass head.2
        let probability := arithmetic .div head.2 mass
        let u := uniform (seed 0)
        let choice := compareLe u.value probability.value
        let visited :=  [.control,.strictComparison 0 mass] ++ nextMass.trace ++ probability.trace ++ u.trace ++ choice.trace ++ [.control]
        if choice.value then ⟨head.1,visited ++ [.control]⟩
        else
          let later := categorical fallback C (next :: tail) nextMass.value (Fin.tail seed)
          ⟨later.value,visited ++ later.trace⟩
      else ⟨head.1,[.control,.strictComparison 0 mass,.control]⟩

 theorem categorical_value {α : Type*} (fallback : α) (C : ℕ) (items : List (α × ℝ))
    (mass : ℝ) (seed : Fin C → ℝ) :
    (categorical fallback C items mass seed).value = realCategoricalReference fallback C items mass seed := by
  induction C generalizing items mass with
  | zero =>
      cases items with
      | nil => rfl
      | cons head rest =>
          cases rest with
          | nil => rfl
          | cons next tail => simp only [categorical,realCategoricalReference]; split_ifs <;> rfl
  | succ C ih =>
      cases items with
      | nil => rfl
      | cons head rest =>
          cases rest with
          | nil => rfl
          | cons next tail =>
              simp only [categorical,realCategoricalReference]
              split
              · simp only [arithmetic,Operation.realValue,RealArithmeticOp.apply,uniform,compareLe]
                by_cases h : seed 0 ≤ head.2 / mass
                · simp [h]
                · simp only [h,ite_false]
                  exact ih _ _ _
              · rfl

 theorem categorical_cost {α : Type*} (fallback : α) (C : ℕ) (items : List (α × ℝ))
    (mass : ℝ) (seed : Fin C → ℝ) : (categorical fallback C items mass seed).cost ≤ 10 * (C + 1) := by
  induction C generalizing items mass with
  | zero =>
      cases items with
      | nil => simp [categorical,Run.cost,Operation.cost]
      | cons head rest =>
          cases rest with
          | nil => simp [categorical,Run.cost,Operation.cost]
          | cons next tail => unfold categorical; split <;> simp [Run.cost,Operation.cost]
  | succ C ih =>
      cases items with
      | nil => simp [categorical,Run.cost,Operation.cost]; omega
      | cons head rest =>
          cases rest with
          | nil => simp [categorical,Run.cost,Operation.cost]; omega
          | cons next tail =>
              unfold categorical
              dsimp only
              split
              · split
                · simp [Run.cost,arithmetic,uniform,compareLe,Operation.cost]
                  omega
                · have h := ih (next :: tail) (mass - head.2) (Fin.tail seed)
                  simp only [arithmetic,Operation.realValue,RealArithmeticOp.apply] at *
                  simp only [Run.cost,List.map_append,List.sum_append,List.map_cons,List.map_nil,
                    List.sum_cons,List.sum_nil,Operation.cost,uniform,compareLe] at *
                  omega
              · simp [Run.cost,Operation.cost]
                omega

noncomputable def point {n : ℕ} (P Q : FixedArrayTable n ℝ) (t : ℝ) : Run (FixedArrayTable n ℝ) :=
  let complement := arithmetic .sub 1 t
  let cells := arrayRun n (fun j =>
    let x := loadReal P j
    let y := loadReal Q j
    let first := arithmetic .mul complement.value x.value
    let second := arithmetic .mul t y.value
    let total := arithmetic .add first.value second.value
    ⟨total.value,x.trace ++ y.trace ++ first.trace ++ second.trace ++ total.trace ++ [.store j.val total.value]⟩)
  ⟨cells.value,complement.trace ++ cells.trace⟩

 theorem point_value {n : ℕ} (P Q : FixedArrayTable n ℝ) (t : ℝ) :
    (point P Q t).value.read = segmentPoint P.read Q.read t := by
  funext j
  simp [point,arrayRun,loadReal,arithmetic,Operation.realValue,RealArithmeticOp.apply,
    FixedArrayTable.read_ofFn,segmentPoint]

 theorem point_cost {n : ℕ} (P Q : FixedArrayTable n ℝ) (t : ℝ) : (point P Q t).cost = 8 * n + 3 := by
  unfold point
  dsimp only
  change cost ([.arithmetic .sub 1 t] ++ _) = _
  rw [cost_append]
  change 1 + (arrayRun n _).cost = _
  rw [arrayRun_cost]
  simp [loadReal,arithmetic,Run.cost,Operation.cost]
  omega

noncomputable def draw {n k : ℕ} (prepared : PreparedSegment n k) (fallback : Fin k)
    (seed : Fin ((k - 1) + 1) → ℝ) : Run (FixedArrayTable n ℝ) :=
  let weights := weightList prepared.weight
  let mass := sumWeights (weights.value.map Prod.snd)
  let slot := categorical fallback (k - 1) weights.value mass.value (Fin.tail seed)
  let t := uniform (seed 0)
  let row := point (prepared.P.read slot.value) (prepared.Q.read slot.value) t.value
  ⟨row.value,weights.trace ++ mass.trace ++ slot.trace ++ t.trace ++
    [.control,.control] ++ row.trace⟩

 theorem draw_cost {n k : ℕ} (prepared : PreparedSegment n k) (fallback : Fin k)
    (seed : Fin ((k - 1) + 1) → ℝ) : (draw prepared fallback seed).cost ≤ 20 * k + 8 * n + 10 := by
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) fallback.isLt
  have hc := categorical_cost fallback (k - 1) (weightList prepared.weight).value
    (sumWeights ((weightList prepared.weight).value.map Prod.snd)).value (Fin.tail seed)
  have hw := weightList_cost prepared.weight
  have hm := sumWeights_cost ((weightList prepared.weight).value.map Prod.snd)
  have hLength : ((weightList prepared.weight).value.map Prod.snd).length = k := by
    simp only [weightList_value,List.length_map,List.length_ofFn]
  rw [hLength] at hm
  have hp := point_cost (prepared.P.read (categorical fallback (k - 1) (weightList prepared.weight).value
    (sumWeights ((weightList prepared.weight).value.map Prod.snd)).value (Fin.tail seed)).value)
    (prepared.Q.read (categorical fallback (k - 1) (weightList prepared.weight).value
    (sumWeights ((weightList prepared.weight).value.map Prod.snd)).value (Fin.tail seed)).value) (seed 0)
  unfold draw
  change cost ((weightList prepared.weight).trace ++ (sumWeights _).trace ++ (categorical _ _ _ _ _).trace ++
    [.uniform (seed 0)] ++ [.control,.control] ++ (point _ _ (seed 0)).trace) ≤ _
  simp only [cost_append,cost_cons,cost_nil,Operation.cost]
  change (weightList prepared.weight).cost + (sumWeights _).cost + (categorical _ _ _ _ _).cost +
    1 + 2 + (point _ _ _).cost ≤ _
  rw [hw,hm,hp]
  omega

 theorem draw_value {n k : ℕ} (l : SegmentLottery n k) (fallback : Fin k)
    (seed : Fin ((k - 1) + 1) → ℝ) :
    (draw (PreparedSegment.ofLottery l) fallback seed).value.read = l.realSampleFlat fallback seed := by
  rw [SegmentLottery.realSampleFlat_refines]
  unfold draw
  dsimp only
  rw [point_value]
  have hChoice : (categorical fallback (k - 1) (weightList (PreparedSegment.ofLottery l).weight).value
      (sumWeights ((weightList (PreparedSegment.ofLottery l).weight).value.map Prod.snd)).value (Fin.tail seed)).value =
      realCategorical l.weight l.nonnegative fallback (Fin.tail seed) := by
    rw [categorical_value,realCategorical_eq_reference,weightList_value,sumWeights_value]
    simp [PreparedSegment.ofLottery,FixedArrayTable.read_ofFn,List.map_ofFn,List.sum_ofFn]
  rw [hChoice]
  simp only [PreparedSegment.ofLottery,FixedArrayTable.read_ofFn,uniform,Operation.realValue]
  funext j
  simp [segmentPoint,SegmentLottery.point,FixedArrayTable.read_ofFn]

 theorem draw_law {n k : ℕ} (l : SegmentLottery n k) (fallback : Fin k) :
    Measure.map (fun seed => (draw (PreparedSegment.ofLottery l) fallback seed).value.read)
      (RealUniformInputs.law ((k - 1) + 1) : Measure (Fin ((k - 1) + 1) → ℝ)) =
        (l.law : Measure (Allocation n)) := by
  have h : (fun seed => (draw (PreparedSegment.ofLottery l) fallback seed).value.read) = l.realSampleFlat fallback :=
    funext (draw_value l fallback)
  rw [h]
  exact l.realSampleFlat_law fallback

 theorem draw_fullBudget {n k : ℕ} (l : SegmentLottery n k) (fallback : Fin k) (B : ℝ)
    (hP : ∀ slot, FullBudget B (l.P slot)) (hQ : ∀ slot, FullBudget B (l.Q slot))
    (seed : Fin ((k - 1) + 1) → ℝ) (ht : 0 ≤ seed 0 ∧ seed 0 ≤ 1) :
    FullBudget B (draw (PreparedSegment.ofLottery l) fallback seed).value.read := by
  rw [draw_value]
  exact l.realSampleFlat_fullBudget fallback hP hQ seed ht

end Blotto.PRGRealRAMExecution

namespace Blotto.PRGExactRealRAMContract
open MeasureTheory
open PRGRealRAMExecution
open scoped BigOperators Classical

 theorem table_ext {α : Type*} {n : ℕ} (a b : FixedArrayTable n α)
    (h : ∀ j, a.read j = b.read j) : a = b := by
  have hd : a.data = b.data := by
    apply Array.ext
    · exact a.size.trans b.size.symm
    · intro j hj hk
      exact h ⟨j,by simpa only [a.size] using hj⟩
  cases a
  cases b
  cases hd
  rfl

 theorem prepared_ext {n k : ℕ} (a b : PreparedSegment n k)
    (hw : a.weight = b.weight) (hP : a.P = b.P) (hQ : a.Q = b.Q) : a = b := by
  cases a
  cases b
  cases hw
  cases hP
  cases hQ
  rfl

 theorem arrayRun_bound {α : Type*} (n B : ℕ) (body : Fin n → Run α)
    (h : ∀ j, (body j).cost ≤ B) : (arrayRun n body).cost ≤ 2 + n * (B + 2) := by
  rw [arrayRun_cost]
  exact Nat.add_le_add_left ((Finset.sum_le_sum (fun j _ => Nat.add_le_add_right (h j) 2)).trans_eq
    (by simp)) 2

noncomputable def assemble {n k : ℕ} (weight : Run (FixedArrayTable k ℝ))
    (P Q : Run (FixedArrayTable k (FixedArrayTable n ℝ))) : Run (PreparedSegment n k) :=
  ⟨⟨weight.value,P.value,Q.value⟩,weight.trace ++ P.trace ++ Q.trace ++ [.control,.control,.control]⟩

 theorem assemble_cost {n k : ℕ} (weight : Run (FixedArrayTable k ℝ))
    (P Q : Run (FixedArrayTable k (FixedArrayTable n ℝ))) :
    (assemble weight P Q).cost = weight.cost + P.cost + Q.cost + 3 := by
  unfold assemble Run.cost
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Operation.cost]
  omega

/-- A complete descriptor producer: every weight and endpoint coordinate is
produced by the counted real expression interpreter and stored once. -/
noncomputable def geometryFactory (env : FixedArrayTable 4 ℝ) : Run (PreparedSegment 3 9) :=
  assemble
    (arrayRun 9 (fun slot => expression env (RationalThreeGeometryCode.chosen slot)))
    (arrayRun 9 (fun slot => arrayRun 3 (fun j =>
      expression env (RationalThreeGeometryCode.vertex (threeEdges slot).1 j))))
    (arrayRun 9 (fun slot => arrayRun 3 (fun j =>
      expression env (RationalThreeGeometryCode.vertex (threeEdges slot).2 j))))

 theorem geometryFactory_value (g : ThreeGeometry) :
    (geometryFactory (RealThreeGeometryCode.environment g)).value = PreparedSegment.ofLottery g.segmentLottery := by
  apply prepared_ext
  · apply table_ext
    intro slot
    simp only [geometryFactory,assemble,arrayRun_read,expression_value,PreparedSegment.ofLottery,
      FixedArrayTable.read_ofFn,RealThreeGeometryCode.chosen_value,ThreeGeometry.segmentLottery]
  · apply table_ext
    intro slot
    apply table_ext
    intro j
    simp only [geometryFactory,assemble,arrayRun_read,expression_value,PreparedSegment.ofLottery,
      FixedArrayTable.read_ofFn,RealThreeGeometryCode.vertex_value,ThreeGeometry.segmentLottery]
  · apply table_ext
    intro slot
    apply table_ext
    intro j
    simp only [geometryFactory,assemble,arrayRun_read,expression_value,PreparedSegment.ofLottery,
      FixedArrayTable.read_ofFn,RealThreeGeometryCode.vertex_value,ThreeGeometry.segmentLottery]

 theorem geometryFactory_cost (env : FixedArrayTable 4 ℝ) : (geometryFactory env).cost ≤ 6000 := by
  have hw := arrayRun_bound 9 512 (fun slot => expression env (RationalThreeGeometryCode.chosen slot))
    (fun slot => (expression_cost env _).trans (Nat.mul_le_mul_left 2 (RationalThreeGeometryCode.chosen_operationBound slot)))
  have hv : ∀ (vertex : Fin 6), (arrayRun 3 (fun j => expression env (RationalThreeGeometryCode.vertex vertex j))).cost ≤ 56 := by
    intro vertex
    exact arrayRun_bound 3 16 _ (fun j => (expression_cost env _).trans
      (Nat.mul_le_mul_left 2 (RationalThreeGeometryCode.vertex_operationBound vertex j)))
  have hP := arrayRun_bound 9 56 (fun slot => arrayRun 3 (fun j => expression env (RationalThreeGeometryCode.vertex (threeEdges slot).1 j)))
    (fun slot => hv (threeEdges slot).1)
  have hQ := arrayRun_bound 9 56 (fun slot => arrayRun 3 (fun j => expression env (RationalThreeGeometryCode.vertex (threeEdges slot).2 j)))
    (fun slot => hv (threeEdges slot).2)
  unfold geometryFactory
  rw [assemble_cost]
  omega

noncomputable def inputEnvironment (i : ThreeInput) : Run (FixedArrayTable 5 ℝ) :=
  arrayRun 5 (fun j =>
    let value := ![i.B,i.a,i.d,i.c,i.p] j
    ⟨value,[.load j.val value]⟩)

 theorem inputEnvironment_value (i : ThreeInput) : (inputEnvironment i).value = RealThreeInputPreparationCode.environment i := by
  apply table_ext
  intro j
  simp [inputEnvironment,RealThreeInputPreparationCode.environment,FixedArrayTable.read_ofFn]

 theorem inputEnvironment_cost (i : ThreeInput) : (inputEnvironment i).cost = 17 := by
  unfold inputEnvironment
  rw [arrayRun_cost]
  simp [Run.cost,Operation.cost]

noncomputable def parameters (env : FixedArrayTable 5 ℝ) : Run (FixedArrayTable 4 ℝ) :=
  arrayRun 4 (fun j => expression env (RationalThreeInputCode.parameters j))

 theorem parameters_value (i : ThreeInput) (hE : 0 < i.a + i.d - i.B) :
    (parameters (inputEnvironment i).value).value = RealThreeGeometryCode.environment (i.geometry hE) := by
  apply table_ext
  intro j
  simp only [parameters,arrayRun_read,expression_value,inputEnvironment_value]
  exact RealThreeInputPreparationCode.parameter_value i hE j

 theorem parameters_cost (env : FixedArrayTable 5 ℝ) : (parameters env).cost ≤ 74 :=
  arrayRun_bound 4 16 _ (fun j => (expression_cost env _).trans
    (Nat.mul_le_mul_left 2 (RationalThreeInputCode.parameter_operations j)))

noncomputable def exceptionalFactory (i : ThreeInput) : Run (PreparedSegment 3 9) :=
  assemble
    (arrayRun 9 (fun slot => ⟨if slot = 0 then 1 else 0,[.control,.load slot.val (if slot = 0 then 1 else 0)]⟩))
    (arrayRun 9 (fun _ => arrayRun 3 (fun j => ⟨![0,0,i.B] j,[.load j.val (![0,0,i.B] j)]⟩)))
    (arrayRun 9 (fun _ => arrayRun 3 (fun j => ⟨![i.a,i.d,0] j,[.load j.val (![i.a,i.d,0] j)]⟩)))

 theorem exceptionalFactory_value (i : ThreeInput) (hE : ¬0 < i.a + i.d - i.B) :
    (exceptionalFactory i).value = PreparedSegment.ofLottery i.segmentLottery := by
  apply prepared_ext
  · apply table_ext
    intro slot
    simp [exceptionalFactory,assemble,arrayRun_read,PreparedSegment.ofLottery,ThreeInput.segmentLottery,hE,
      FixedArrayTable.read_ofFn]
  · apply table_ext
    intro slot
    apply table_ext
    intro j
    simp [exceptionalFactory,assemble,arrayRun_read,PreparedSegment.ofLottery,ThreeInput.segmentLottery,hE,
      FixedArrayTable.read_ofFn]
  · apply table_ext
    intro slot
    apply table_ext
    intro j
    simp [exceptionalFactory,assemble,arrayRun_read,PreparedSegment.ofLottery,ThreeInput.segmentLottery,hE,
      FixedArrayTable.read_ofFn]

 theorem exceptionalFactory_cost (i : ThreeInput) : (exceptionalFactory i).cost ≤ 300 := by
  have hw := arrayRun_bound 9 2 (fun slot : Fin 9 =>
    (⟨if slot = 0 then 1 else 0,[.control,.load slot.val (if slot = 0 then 1 else 0)]⟩ : Run ℝ)) (fun _ => by rfl)
  have hp := arrayRun_bound 9 11 (fun _ : Fin 9 => arrayRun 3 (fun j : Fin 3 =>
    (⟨![0,0,i.B] j,[.load j.val (![0,0,i.B] j)]⟩ : Run ℝ)))
    (fun _ => arrayRun_bound 3 1 _ (fun _ => by rfl))
  have hq := arrayRun_bound 9 11 (fun _ : Fin 9 => arrayRun 3 (fun j : Fin 3 =>
    (⟨![i.a,i.d,0] j,[.load j.val (![i.a,i.d,0] j)]⟩ : Run ℝ)))
    (fun _ => arrayRun_bound 3 1 _ (fun _ => by rfl))
  unfold exceptionalFactory
  rw [assemble_cost]
  omega

noncomputable def orderedFactory (i : ThreeInput) : Run (PreparedSegment 3 9) :=
  let env := inputEnvironment i
  let regime := expression env.value RationalThreeInputCode.regime
  if 0 < regime.value then
    let fields := parameters env.value
    let result := geometryFactory fields.value
    ⟨result.value,env.trace ++ regime.trace ++ [.strictComparison 0 regime.value,.control] ++ fields.trace ++ result.trace⟩
  else
    let result := exceptionalFactory i
    ⟨result.value,env.trace ++ regime.trace ++ [.strictComparison 0 regime.value,.control] ++ result.trace⟩

 theorem orderedFactory_value (i : ThreeInput) : (orderedFactory i).value = PreparedSegment.ofLottery i.segmentLottery := by
  have hRegime : (expression (inputEnvironment i).value RationalThreeInputCode.regime).value = i.a + i.d - i.B := by
    rw [expression_value,inputEnvironment_value]
    exact RealThreeInputPreparationCode.regime_value i
  unfold orderedFactory
  dsimp only
  rw [hRegime]
  split
  · rename_i hE
    rw [parameters_value i hE,geometryFactory_value]
    simp only [ThreeInput.segmentLottery,dite_eq_left hE]
  · exact exceptionalFactory_value i ‹¬0 < i.a + i.d - i.B›

 theorem orderedFactory_cost (i : ThreeInput) : (orderedFactory i).cost ≤ 6300 := by
  have hEnv := inputEnvironment_cost i
  have hRegime : (expression (inputEnvironment i).value RationalThreeInputCode.regime).cost ≤ 10 :=
    (expression_cost _ _).trans (by decide)
  have hFields := parameters_cost (inputEnvironment i).value
  have hGeometry := geometryFactory_cost (parameters (inputEnvironment i).value).value
  have hExceptional := exceptionalFactory_cost i
  unfold orderedFactory
  dsimp only
  split <;> change cost _ ≤ _
  · simp only [cost_append,cost_cons,cost_nil,Operation.cost]
    change (inputEnvironment i).cost + (expression _ _).cost + 2 + (parameters _).cost + (geometryFactory _).cost ≤ _
    omega
  · simp only [cost_append,cost_cons,cost_nil,Operation.cost]
    change (inputEnvironment i).cost + (expression _ _).cost + 2 + (exceptionalFactory i).cost ≤ _
    omega

noncomputable def orderedDraw (i : ThreeInput) (seed : Fin 9 → ℝ) : Run (FixedArrayTable 3 ℝ) :=
  let prepared := orderedFactory i
  let result := draw prepared.value 0 seed
  ⟨result.value,prepared.trace ++ result.trace⟩

 theorem orderedDraw_value (i : ThreeInput) (seed : Fin 9 → ℝ) :
    (orderedDraw i seed).value.read = i.segmentLottery.realSampleFlat 0 seed := by
  unfold orderedDraw
  dsimp only
  rw [orderedFactory_value]
  exact draw_value i.segmentLottery 0 seed

 theorem orderedDraw_cost (i : ThreeInput) (seed : Fin 9 → ℝ) : (orderedDraw i seed).cost ≤ 7000 := by
  have hf := orderedFactory_cost i
  have hd := draw_cost (orderedFactory i).value 0 seed
  unfold orderedDraw
  change cost ((orderedFactory i).trace ++ (draw (orderedFactory i).value 0 seed).trace) ≤ _
  rw [cost_append]
  change (orderedFactory i).cost + (draw (orderedFactory i).value 0 seed).cost ≤ _
  omega

 theorem orderedDraw_law (i : ThreeInput) :
    Measure.map (fun seed => (orderedDraw i seed).value.read)
      (RealUniformInputs.law 9 : Measure (Fin 9 → ℝ)) = (i.couplingLaw : Measure (Allocation 3)) := by
  have h : (fun seed => (orderedDraw i seed).value.read) = i.segmentLottery.realSampleFlat 0 := funext (orderedDraw_value i)
  rw [h,i.segmentLottery.realSampleFlat_law 0]
  exact i.segmentLottery_law

 theorem orderedDraw_fullBudget (i : ThreeInput) (seed : Fin 9 → ℝ) (ht : 0 ≤ seed 0 ∧ seed 0 ≤ 1) :
    FullBudget i.B (orderedDraw i seed).value.read := by
  rw [orderedDraw_value]
  exact i.segmentLottery.realSampleFlat_fullBudget 0 i.segmentLottery_endpoints.1 i.segmentLottery_endpoints.2 seed ht


end Blotto.PRGExactRealRAMContract
