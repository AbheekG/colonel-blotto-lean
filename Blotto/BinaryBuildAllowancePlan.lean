import Blotto.BinaryPhysicalBuildAllowanceMeasured
import Blotto.BinaryCachePrefixPlan

/-! The actual allowance calculator builds one final-depth trace plan through
its full-adder, schoolbook products and node-word loops. Only calculateWithEmission
emits that plan. Count/reversal leaf traces, observer arithmetic and native
scalar/reference/allocator costs retain their preceding scopes. -/
namespace Blotto.BinaryBuildAllowancePlan
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth
open BinaryTracePlanMeasured
open BinaryCachePrefixPlan (observe offset data_of_refinement trace_of_refinement
  work_of_refinement Bounded block_bound)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def addLoopAt : List Bool → List Bool → Bool → List Bool → ℕ → (List Bool × Plan) × ℕ
  | [],[],carry,acc,depth =>
      let reversed := BinarySeedCursorMeasured.reverseAt (if carry then true::acc else acc) [] (depth+2)
      ((reversed.1.1,.join (.block [.listAllocation (if carry then 1 else 0),
        .frames (depth+1),.arrayAllocation 8]) (.block reversed.1.2)),reversed.2+(if carry then 16 else 20))
  | a::rest,[],carry,acc,depth =>
      let later := addLoopAt rest [] (BinaryAddition.nextCarry a false carry)
        (BinaryAddition.sumBit a false carry::acc) (depth+2)
      ((later.1.1,.join (.block [.listAllocation 1,.frames (depth+2),.arrayAllocation 8]) later.1.2),later.2+18)
  | [],b::rest,carry,acc,depth =>
      let later := addLoopAt [] rest (BinaryAddition.nextCarry false b carry)
        (BinaryAddition.sumBit false b carry::acc) (depth+2)
      ((later.1.1,.join (.block [.listAllocation 1,.frames (depth+2),.arrayAllocation 8]) later.1.2),later.2+18)
  | a::as,b::bs,carry,acc,depth =>
      let later := addLoopAt as bs (BinaryAddition.nextCarry a b carry)
        (BinaryAddition.sumBit a b carry::acc) (depth+2)
      ((later.1.1,.join (.block [.listAllocation 1,.frames (depth+2),.arrayAllocation 8]) later.1.2),later.2+18)

theorem addLoop_refines (a b : List Bool) (carry : Bool) (acc : List Bool) (depth : ℕ) :
    observe (addLoopAt a b carry acc depth) = offset depth (BinaryBuildAllowanceArithmeticMeasured.addLoop a b carry acc) := by
  induction a generalizing b carry acc depth with
  | nil =>
      induction b generalizing carry acc depth with
      | nil =>
          simp only [addLoopAt,BinaryBuildAllowanceArithmeticMeasured.addLoop,observe,offset,denote,
            BinarySeedCursorMeasured.reverseAt_erases,BinarySeedCursorMeasured.reverse_erases,
            BinarySeedCursorMeasured.reverseAt_work,BinarySeedCursorMeasured.reverse_work,
            wrapList,wrap,combine,List.append_nil,under_append,under_compose]
          rfl
      | cons bit rest ih =>
          have h := ih (BinaryAddition.nextCarry false bit carry) (BinaryAddition.sumBit false bit carry::acc) (depth+2)
          simp only [addLoopAt,BinaryBuildAllowanceArithmeticMeasured.addLoop,observe,offset,denote,
            data_of_refinement h,trace_of_refinement h,work_of_refinement h,
            wrapList,wrap,combine,List.append_nil,under_append,under_compose]
          rfl
  | cons bit rest ih => cases b with
    | nil =>
        have h := ih [] (BinaryAddition.nextCarry bit false carry) (BinaryAddition.sumBit bit false carry::acc) (depth+2)
        simp only [addLoopAt,BinaryBuildAllowanceArithmeticMeasured.addLoop,observe,offset,denote,
          data_of_refinement h,trace_of_refinement h,work_of_refinement h,
          wrapList,wrap,combine,List.append_nil,under_append,under_compose]
        rfl
    | cons other tail =>
        have h := ih tail (BinaryAddition.nextCarry bit other carry) (BinaryAddition.sumBit bit other carry::acc) (depth+2)
        simp only [addLoopAt,BinaryBuildAllowanceArithmeticMeasured.addLoop,observe,offset,denote,
          data_of_refinement h,trace_of_refinement h,work_of_refinement h,
          wrapList,wrap,combine,List.append_nil,under_append,under_compose]
        rfl

theorem addLoop_bound (a b : List Bool) (carry : Bool) (acc : List Bool) (depth : ℕ) :
    Bounded (addLoopAt a b carry acc depth).1.2 := by
  induction a generalizing b carry acc depth with
  | nil =>
      induction b generalizing carry acc depth with
      | nil =>
          simp only [Bounded,addLoopAt,nodes,payload,List.length_cons,List.length_nil]
          omega
      | cons bit rest ih =>
          have h := ih (BinaryAddition.nextCarry false bit carry) (BinaryAddition.sumBit false bit carry::acc) (depth+2)
          simp only [Bounded,addLoopAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
          omega
  | cons bit rest ih => cases b with
    | nil =>
        have h := ih [] (BinaryAddition.nextCarry bit false carry) (BinaryAddition.sumBit bit false carry::acc) (depth+2)
        simp only [Bounded,addLoopAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
        omega
    | cons other tail =>
        have h := ih tail (BinaryAddition.nextCarry bit other carry) (BinaryAddition.sumBit bit other carry::acc) (depth+2)
        simp only [Bounded,addLoopAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
        omega

theorem addLoop_payload (a b : List Bool) (carry : Bool) (acc : List Bool) (depth : ℕ) :
    payload (addLoopAt a b carry acc depth).1.2 ≤ 2*(addLoopAt a b carry acc depth).2 := by
  induction a generalizing b carry acc depth with
  | nil =>
      induction b generalizing carry acc depth with
      | nil =>
          simp only [addLoopAt,payload,List.length_cons,List.length_nil,
            BinarySeedCursorMeasured.reverseAt_trace_length,BinarySeedCursorMeasured.reverseAt_work,
            BinaryMidpointTapeLifetime.reverse_work]
          split <;> omega
      | cons bit rest ih =>
          have h := ih (BinaryAddition.nextCarry false bit carry) (BinaryAddition.sumBit false bit carry::acc) (depth+2)
          simp only [addLoopAt,payload,List.length_cons,List.length_nil] at h ⊢
          omega
  | cons bit rest ih => cases b with
    | nil =>
        have h := ih [] (BinaryAddition.nextCarry bit false carry) (BinaryAddition.sumBit bit false carry::acc) (depth+2)
        simp only [addLoopAt,payload,List.length_cons,List.length_nil] at h ⊢
        omega
    | cons other tail =>
        have h := ih tail (BinaryAddition.nextCarry bit other carry) (BinaryAddition.sumBit bit other carry::acc) (depth+2)
        simp only [addLoopAt,payload,List.length_cons,List.length_nil] at h ⊢
        omega

def addAt (a b : List Bool) (depth : ℕ) : (List Bool × Plan) × ℕ := addLoopAt a b false [] depth

theorem add_refines (a b : List Bool) (depth : ℕ) :
    observe (addAt a b depth) = offset depth (BinaryBuildAllowanceArithmeticMeasured.add a b) :=
  addLoop_refines a b false [] depth

theorem add_bound (a b : List Bool) (depth : ℕ) : Bounded (addAt a b depth).1.2 :=
  addLoop_bound a b false [] depth

theorem add_payload (a b : List Bool) (depth : ℕ) :
    payload (addAt a b depth).1.2 ≤ 2*(addAt a b depth).2 := addLoop_payload a b false [] depth

theorem add_data (a b : List Bool) (depth : ℕ) :
    (addAt a b depth).1.1 = (BinaryBuildAllowanceArithmeticMeasured.add a b).1.1 :=
  data_of_refinement (add_refines a b depth)

theorem add_trace (a b : List Bool) (depth : ℕ) :
    denote (addAt a b depth).1.2 = under depth (BinaryBuildAllowanceArithmeticMeasured.add a b).1.2 :=
  trace_of_refinement (add_refines a b depth)

theorem add_work (a b : List Bool) (depth : ℕ) :
    (addAt a b depth).2 = (BinaryBuildAllowanceArithmeticMeasured.add a b).2 :=
  work_of_refinement (add_refines a b depth)

def multiplyAt : List Bool → List Bool → ℕ → (List Bool × Plan) × ℕ
  | [],_,depth => (([],.block [.frames (depth+1),.arrayAllocation 8]),1)
  | bit::rest,other,depth =>
      let earlier := multiplyAt rest other (depth+2)
      let shifted := false::earlier.1.1
      if bit then
        let added := addAt other shifted (depth+2)
        ((added.1.1,.join (.block [.listAllocation 1,.frames (depth+2),.arrayAllocation 16])
          (.join earlier.1.2 added.1.2)),earlier.2+3+added.2)
      else ((shifted,.join (.block [.listAllocation 1,.frames (depth+2),.arrayAllocation 8]) earlier.1.2),earlier.2+3)

theorem multiply_refines (a b : List Bool) (depth : ℕ) :
    observe (multiplyAt a b depth) = offset depth (BinaryBuildAllowanceArithmeticMeasured.multiply a b) := by
  induction a generalizing depth with
  | nil => rfl
  | cons bit rest ih =>
      have h := ih (depth+2)
      cases bit <;> simp only [multiplyAt,BinaryBuildAllowanceArithmeticMeasured.multiply,observe,offset,denote,
        Bool.false_eq_true,ite_false,ite_true,data_of_refinement h,trace_of_refinement h,work_of_refinement h,
        add_data,add_trace,add_work,wrapList,wrap,combine,List.append_nil,under_append,under_compose] <;> rfl

theorem multiply_bound (a b : List Bool) (depth : ℕ) : Bounded (multiplyAt a b depth).1.2 := by
  induction a generalizing depth with
  | nil => exact block_bound _
  | cons bit rest ih =>
      have h := ih (depth+2)
      have ha := add_bound b (false::(multiplyAt rest b (depth+2)).1.1) (depth+2)
      cases bit <;> simp only [Bounded,multiplyAt,nodes,payload,Bool.false_eq_true,ite_false,ite_true,
        List.length_cons,List.length_nil] at h ha ⊢ <;> omega

theorem multiply_payload (a b : List Bool) (depth : ℕ) :
    payload (multiplyAt a b depth).1.2 ≤ 2*(multiplyAt a b depth).2 := by
  induction a generalizing depth with
  | nil => simp [multiplyAt,payload]
  | cons bit rest ih =>
      have h := ih (depth+2)
      have ha := add_payload b (false::(multiplyAt rest b (depth+2)).1.1) (depth+2)
      cases bit <;> simp only [multiplyAt,payload,Bool.false_eq_true,ite_false,ite_true,
        List.length_cons,List.length_nil] at h ha ⊢ <;> omega

theorem multiply_data (a b : List Bool) (depth : ℕ) :
    (multiplyAt a b depth).1.1 = (BinaryBuildAllowanceArithmeticMeasured.multiply a b).1.1 :=
  data_of_refinement (multiply_refines a b depth)

theorem multiply_trace (a b : List Bool) (depth : ℕ) :
    denote (multiplyAt a b depth).1.2 = under depth (BinaryBuildAllowanceArithmeticMeasured.multiply a b).1.2 :=
  trace_of_refinement (multiply_refines a b depth)

theorem multiply_work (a b : List Bool) (depth : ℕ) :
    (multiplyAt a b depth).2 = (BinaryBuildAllowanceArithmeticMeasured.multiply a b).2 :=
  work_of_refinement (multiply_refines a b depth)

def nodesAt : List Bool → ℕ → (List Bool × Plan) × ℕ
  | [],depth => (([true],.block [.listAllocation 1,.frames (depth+1),.arrayAllocation 8]),2)
  | _::rest,depth =>
      let later := nodesAt rest (depth+2)
      ((true::later.1.1,.join (.block [.listAllocation 1,.frames (depth+1),.arrayAllocation 8]) later.1.2),later.2+2)

theorem nodes_refines (ruler : List Bool) (depth : ℕ) :
    observe (nodesAt ruler depth) = offset depth (BinaryBuildAllowanceArithmeticMeasured.nodes ruler) := by
  induction ruler generalizing depth with
  | nil => rfl
  | cons bit rest ih =>
      have h := ih (depth+2)
      simp only [nodesAt,BinaryBuildAllowanceArithmeticMeasured.nodes,observe,offset,denote,
        data_of_refinement h,trace_of_refinement h,work_of_refinement h,
        wrapList,wrap,combine,List.append_nil,under_append,under_compose]
      rfl

theorem nodes_bound (ruler : List Bool) (depth : ℕ) : Bounded (nodesAt ruler depth).1.2 := by
  induction ruler generalizing depth with
  | nil => exact block_bound _
  | cons bit rest ih =>
      have h := ih (depth+2)
      simp only [Bounded,nodesAt,nodes,payload,List.length_cons,List.length_nil] at h ⊢
      omega

theorem nodes_payload (ruler : List Bool) (depth : ℕ) :
    payload (nodesAt ruler depth).1.2 ≤ 2*(nodesAt ruler depth).2 := by
  induction ruler generalizing depth with
  | nil => simp [nodesAt,payload]
  | cons bit rest ih =>
      have h := ih (depth+2)
      simp only [nodesAt,payload,List.length_cons,List.length_nil] at h ⊢
      omega

theorem nodes_data (ruler : List Bool) (depth : ℕ) :
    (nodesAt ruler depth).1.1 = (BinaryBuildAllowanceArithmeticMeasured.nodes ruler).1.1 :=
  data_of_refinement (nodes_refines ruler depth)

theorem nodes_trace (ruler : List Bool) (depth : ℕ) :
    denote (nodesAt ruler depth).1.2 = under depth (BinaryBuildAllowanceArithmeticMeasured.nodes ruler).1.2 :=
  trace_of_refinement (nodes_refines ruler depth)

theorem nodes_work (ruler : List Bool) (depth : ℕ) :
    (nodesAt ruler depth).2 = (BinaryBuildAllowanceArithmeticMeasured.nodes ruler).2 :=
  work_of_refinement (nodes_refines ruler depth)

theorem count_data {α : Type*} (items : List α) (counter : List Bool) (depth : ℕ) :
    (BinaryHeapAllocationMeasured.countAt items counter depth).1.1 = (BinaryHeapAllocationMeasured.count items counter).1.1 := by
  rw [BinaryHeapAllocationMeasured.countAt_erases,BinaryHeapAllocationMeasured.count_erases]

theorem count_trace {α : Type*} (items : List α) (counter : List Bool) (depth : ℕ) :
    (BinaryHeapAllocationMeasured.countAt items counter depth).1.2 = under depth (BinaryHeapAllocationMeasured.count items counter).1.2 := by
  rw [BinaryHeapAllocationMeasured.countAt_erases,BinaryHeapAllocationMeasured.count_erases]

theorem count_work {α : Type*} (items : List α) (counter : List Bool) (depth : ℕ) :
    (BinaryHeapAllocationMeasured.countAt items counter depth).2.work = (BinaryHeapAllocationMeasured.count items counter).2.work := by
  rw [BinaryHeapAllocationMeasured.countAt_charge,BinaryHeapAllocationMeasured.count_charge]

def treeAt (nodeWord tape : List Bool) (depth : ℕ) : (List Bool × Plan) × ℕ :=
  let counted := BinaryHeapAllocationMeasured.countAt tape [true] (depth+2)
  let square := multiplyAt counted.1.1 counted.1.1 (depth+2)
  let scaled := multiplyAt BinaryPhysicalBuildAllowance.hundred square.1.1 (depth+2)
  let allocation := addAt scaled.1.1 BinaryPhysicalBuildAllowance.eight (depth+2)
  let product := multiplyAt nodeWord allocation.1.1 (depth+2)
  ((product.1.1,.join (.block [.listAllocation 11,.frames (depth+4),.arrayAllocation 64])
    (.join (.block counted.1.2) (.join square.1.2 (.join scaled.1.2 (.join allocation.1.2 product.1.2))))),
    counted.2.work+square.2+scaled.2+allocation.2+product.2+16)

theorem tree_refines (nodeWord tape : List Bool) (depth : ℕ) :
    observe (treeAt nodeWord tape depth) = offset depth (BinaryPhysicalBuildAllowanceMeasured.tree nodeWord tape) := by
  simp only [treeAt,BinaryPhysicalBuildAllowanceMeasured.tree,observe,offset,denote,
    count_data,count_trace,count_work,multiply_data,multiply_trace,multiply_work,add_data,add_trace,add_work,
    wrapList,wrap,combine,List.append_nil,under_append,under_compose]
  rfl

theorem tree_data (nodeWord tape : List Bool) (depth : ℕ) :
    (treeAt nodeWord tape depth).1.1 = (BinaryPhysicalBuildAllowanceMeasured.tree nodeWord tape).1.1 :=
  data_of_refinement (tree_refines nodeWord tape depth)

theorem tree_trace (nodeWord tape : List Bool) (depth : ℕ) :
    denote (treeAt nodeWord tape depth).1.2 = under depth (BinaryPhysicalBuildAllowanceMeasured.tree nodeWord tape).1.2 :=
  trace_of_refinement (tree_refines nodeWord tape depth)

theorem tree_work (nodeWord tape : List Bool) (depth : ℕ) :
    (treeAt nodeWord tape depth).2 = (BinaryPhysicalBuildAllowanceMeasured.tree nodeWord tape).2 :=
  work_of_refinement (tree_refines nodeWord tape depth)

theorem tree_bound (nodeWord tape : List Bool) (depth : ℕ) :
    Bounded (treeAt nodeWord tape depth).1.2 := by
  let counted := BinaryHeapAllocationMeasured.countAt tape [true] (depth+2)
  let square := multiplyAt counted.1.1 counted.1.1 (depth+2)
  let scaled := multiplyAt BinaryPhysicalBuildAllowance.hundred square.1.1 (depth+2)
  let allocation := addAt scaled.1.1 BinaryPhysicalBuildAllowance.eight (depth+2)
  have hs := multiply_bound counted.1.1 counted.1.1 (depth+2)
  change nodes square.1.2 ≤ 4*payload square.1.2+1 at hs
  have hc := multiply_bound BinaryPhysicalBuildAllowance.hundred square.1.1 (depth+2)
  change nodes scaled.1.2 ≤ 4*payload scaled.1.2+1 at hc
  have ha := add_bound scaled.1.1 BinaryPhysicalBuildAllowance.eight (depth+2)
  change nodes allocation.1.2 ≤ 4*payload allocation.1.2+1 at ha
  have hp := multiply_bound nodeWord allocation.1.1 (depth+2)
  change Bounded (.join (.block _) (.join (.block _) (.join square.1.2
    (.join scaled.1.2 (.join allocation.1.2 (multiplyAt nodeWord allocation.1.1 (depth+2)).1.2)))))
  simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at hp ⊢
  omega

theorem tree_payload (nodeWord tape : List Bool) (depth : ℕ) :
    payload (treeAt nodeWord tape depth).1.2 ≤ 2*(treeAt nodeWord tape depth).2 := by
  let counted := BinaryHeapAllocationMeasured.countAt tape [true] (depth+2)
  let square := multiplyAt counted.1.1 counted.1.1 (depth+2)
  let scaled := multiplyAt BinaryPhysicalBuildAllowance.hundred square.1.1 (depth+2)
  let allocation := addAt scaled.1.1 BinaryPhysicalBuildAllowance.eight (depth+2)
  have hCount := BinaryHeapAllocationMeasured.countAt_trace_work tape [true] (depth+2)
  change counted.1.2.length ≤ 2*counted.2.work at hCount
  have hs := multiply_payload counted.1.1 counted.1.1 (depth+2)
  change payload square.1.2 ≤ 2*square.2 at hs
  have hc := multiply_payload BinaryPhysicalBuildAllowance.hundred square.1.1 (depth+2)
  change payload scaled.1.2 ≤ 2*scaled.2 at hc
  have ha := add_payload scaled.1.1 BinaryPhysicalBuildAllowance.eight (depth+2)
  change payload allocation.1.2 ≤ 2*allocation.2 at ha
  have hp := multiply_payload nodeWord allocation.1.1 (depth+2)
  change 3+(counted.1.2.length+(payload square.1.2+(payload scaled.1.2+
    (payload allocation.1.2+payload (multiplyAt nodeWord allocation.1.1 (depth+2)).1.2)))) ≤
      2*(counted.2.work+square.2+scaled.2+allocation.2+(multiplyAt nodeWord allocation.1.1 (depth+2)).2+16)
  omega

def calculateAt (ruler first second : List Bool) (depth : ℕ) : (List Bool × Plan) × ℕ :=
  let nodeWord := nodesAt ruler (depth+2)
  let a := treeAt nodeWord.1.1 first (depth+2)
  let b := treeAt nodeWord.1.1 second (depth+2)
  let combined := addAt a.1.1 b.1.1 (depth+2)
  ((combined.1.1,.join (.block [.frames (depth+4),.arrayAllocation 64])
    (.join nodeWord.1.2 (.join a.1.2 (.join b.1.2 combined.1.2)))),nodeWord.2+a.2+b.2+combined.2+8)

theorem calculate_refines (ruler first second : List Bool) (depth : ℕ) :
    observe (calculateAt ruler first second depth) = offset depth (BinaryPhysicalBuildAllowanceMeasured.calculate ruler first second) := by
  simp only [calculateAt,BinaryPhysicalBuildAllowanceMeasured.calculate,observe,offset,denote,
    nodes_data,nodes_trace,nodes_work,tree_data,tree_trace,tree_work,add_data,add_trace,add_work,
    wrap,combine,List.append_nil,under_append,under_compose]
  rfl

theorem calculate_bound (ruler first second : List Bool) (depth : ℕ) :
    Bounded (calculateAt ruler first second depth).1.2 := by
  let nodeWord := nodesAt ruler (depth+2)
  let a := treeAt nodeWord.1.1 first (depth+2)
  let b := treeAt nodeWord.1.1 second (depth+2)
  have hn := nodes_bound ruler (depth+2)
  change nodes nodeWord.1.2 ≤ 4*payload nodeWord.1.2+1 at hn
  have ha := tree_bound nodeWord.1.1 first (depth+2)
  change nodes a.1.2 ≤ 4*payload a.1.2+1 at ha
  have hb := tree_bound nodeWord.1.1 second (depth+2)
  change nodes b.1.2 ≤ 4*payload b.1.2+1 at hb
  have hc := add_bound a.1.1 b.1.1 (depth+2)
  change Bounded (.join (.block _) (.join nodeWord.1.2 (.join a.1.2 (.join b.1.2 (addAt a.1.1 b.1.1 (depth+2)).1.2))))
  simp only [Bounded,nodes,payload,List.length_cons,List.length_nil] at hc ⊢
  omega

theorem calculate_payload (ruler first second : List Bool) (depth : ℕ) :
    payload (calculateAt ruler first second depth).1.2 ≤ 2*(calculateAt ruler first second depth).2 := by
  let nodeWord := nodesAt ruler (depth+2)
  let a := treeAt nodeWord.1.1 first (depth+2)
  let b := treeAt nodeWord.1.1 second (depth+2)
  have hn := nodes_payload ruler (depth+2)
  change payload nodeWord.1.2 ≤ 2*nodeWord.2 at hn
  have ha := tree_payload nodeWord.1.1 first (depth+2)
  change payload a.1.2 ≤ 2*a.2 at ha
  have hb := tree_payload nodeWord.1.1 second (depth+2)
  change payload b.1.2 ≤ 2*b.2 at hb
  have hc := add_payload a.1.1 b.1.1 (depth+2)
  change 2+(payload nodeWord.1.2+(payload a.1.2+(payload b.1.2+
    payload (addAt a.1.1 b.1.1 (depth+2)).1.2))) ≤ 2*(nodeWord.2+a.2+b.2+(addAt a.1.1 b.1.1 (depth+2)).2+8)
  omega

def calculateWithEmission (ruler first second : List Bool) : ((List Bool × Trace) × ℕ) × ℕ :=
  let planned := calculateAt ruler first second 0
  let emitted := emitFull planned.1.2 []
  (((planned.1.1,emitted.1.1),planned.2),emitted.1.2+emitted.2)

theorem calculateWithEmission_compat (ruler first second : List Bool) :
    (calculateWithEmission ruler first second).1 = BinaryPhysicalBuildAllowanceMeasured.calculate ruler first second := by
  have h := calculate_refines ruler first second 0
  simpa only [calculateWithEmission,emitFull_erases,emit_data,List.append_nil,observe,offset,under_zero] using h

theorem calculate_plan_size (ruler first second : List Bool) (depth : ℕ) :
    payload (calculateAt ruler first second depth).1.2+nodes (calculateAt ruler first second depth).1.2 ≤
      10*(BinaryPhysicalBuildAllowanceMeasured.calculate ruler first second).2+1 := by
  have hn := calculate_bound ruler first second depth
  have hp := calculate_payload ruler first second depth
  have hw := work_of_refinement (calculate_refines ruler first second depth)
  unfold Bounded at hn
  omega

theorem calculateWithEmission_bound (ruler first second : List Bool) :
    (calculateWithEmission ruler first second).2 ≤ 50*(BinaryPhysicalBuildAllowanceMeasured.calculate ruler first second).2+5 := by
  have h := emitFull_total (calculateAt ruler first second 0).1.2 []
    (10*(BinaryPhysicalBuildAllowanceMeasured.calculate ruler first second).2+1)
    (calculate_plan_size ruler first second 0)
  dsimp only [calculateWithEmission]
  omega

theorem calculateWithEmission_polynomial (ruler first second : List Bool) :
    (calculateWithEmission ruler first second).2 ≤ 1500000*(ruler.length+first.length+second.length+9)^2+5 := by
  have h := calculateWithEmission_bound ruler first second
  have hw := BinaryPhysicalBuildAllowanceMeasured.calculate_bound ruler first second
  omega

theorem calculate_plan_references (ruler first second : List Bool) (depth : ℕ) :
    planReferences (calculateAt ruler first second depth).1.2 ≤
      20*(BinaryPhysicalBuildAllowanceMeasured.calculate ruler first second).2+2 := by
  have h := planReferences_bound (calculateAt ruler first second depth).1.2
  have hs := calculate_plan_size ruler first second depth
  omega

theorem calculate_emit_frames (ruler first second : List Bool) (depth : ℕ) :
    emitFrames (calculateAt ruler first second depth).1.2 ≤
      10*(BinaryPhysicalBuildAllowanceMeasured.calculate ruler first second).2+2 := by
  have h := emitFrames_bound (calculateAt ruler first second depth).1.2
  have hs := calculate_plan_size ruler first second depth
  omega

end Blotto.BinaryBuildAllowancePlan
