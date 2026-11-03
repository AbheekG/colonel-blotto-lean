import Blotto.PRGRealRAMExecution
import Blotto.RealNestedSampler
import Blotto.RealResidualSampler
import Blotto.RealFourSampler
import Blotto.RealSecondUniformPreparation
import Blotto.RealNestedResidualPreparation
import Blotto.RealNestedSpecSampler

namespace Blotto.RealPRGNativeFactoryExecution
open MeasureTheory PRGRealRAMExecution PRGExactRealRAMContract
open scoped BigOperators Classical

noncomputable def join {α β : Type*} (prior : Run α) (result : Run β) : Run β :=
  ⟨result.value,prior.trace ++ result.trace⟩

@[simp] theorem join_value {α β : Type*} (prior : Run α) (result : Run β) :
    (join prior result).value = result.value := rfl

theorem join_cost {α β : Type*} (prior : Run α) (result : Run β) :
    (join prior result).cost = prior.cost + result.cost := by
  change cost (prior.trace ++ result.trace) = _
  exact cost_append _ _

noncomputable def nestedEnvironment (i : NestedInput) (x : ℝ) : Run (FixedArrayTable 7 ℝ) :=
  arrayRun 7 (fun j => let field := ![i.M,i.a,i.d,i.c,i.t,i.q,x] j
    ⟨field,[.load j.val field]⟩)

theorem nestedEnvironment_value (i : NestedInput) (x : ℝ) :
    (nestedEnvironment i x).value = RealNestedParametersCode.environment i x := by
  apply table_ext
  intro j
  simp [nestedEnvironment,RealNestedParametersCode.environment,FixedArrayTable.read_ofFn]

theorem nestedEnvironment_cost (i : NestedInput) (x : ℝ) : (nestedEnvironment i x).cost = 23 := by
  unfold nestedEnvironment
  rw [arrayRun_cost]
  simp [Run.cost,Operation.cost]

noncomputable def firstParameters (env : FixedArrayTable 7 ℝ) : Run (FixedArrayTable 4 ℝ) :=
  arrayRun 4 (fun j => expression env (RationalNestedParametersCode.firstParameters j))

theorem firstParameters_value (i : NestedInput) (htv : i.t ≤ i.v) (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ i.t) (hp : 0 < i.conditionalProbability x) :
    (firstParameters (nestedEnvironment i x).value).value =
      RealThreeGeometryCode.environment (i.firstGeometry htv x hx hp) := by
  apply table_ext
  intro j
  simp only [firstParameters,arrayRun_read,expression_value,nestedEnvironment_value]
  exact RealNestedParametersCode.firstParameters_value i htv x hx hp j

theorem firstParameters_cost (env : FixedArrayTable 7 ℝ) : (firstParameters env).cost ≤ 138 :=
  arrayRun_bound 4 32 _ (fun j => (expression_cost env _).trans
    (Nat.mul_le_mul_left 2 (RationalNestedParametersCode.first_parameter_operationBound j)))

noncomputable def residualEnvironment (r : NestedResidual) : Run (FixedArrayTable 5 ℝ) :=
  arrayRun 5 (fun j => let field := ![r.g.u,r.g.v,r.g.w,r.g.h,r.t] j
    ⟨field,[.load j.val field]⟩)

theorem residualEnvironment_value (r : NestedResidual) :
    (residualEnvironment r).value = RealNestedResidualCode.environment r := by
  apply table_ext
  intro j
  simp [residualEnvironment,RealNestedResidualCode.environment,FixedArrayTable.read_ofFn]

theorem residualEnvironment_cost (r : NestedResidual) : (residualEnvironment r).cost = 17 := by
  unfold residualEnvironment
  rw [arrayRun_cost]
  simp [Run.cost,Operation.cost]

noncomputable def residualDescriptor (env : FixedArrayTable 5 ℝ) : Run (PreparedSegment 3 3) :=
  assemble
    (arrayRun 3 (fun slot => expression env (RationalNestedResidualCode.weights slot)))
    (arrayRun 3 (fun slot => arrayRun 3 (fun j =>
      expression env (RationalNestedResidualCode.vertices (NestedResidual.edges slot).1 j))))
    (arrayRun 3 (fun slot => arrayRun 3 (fun j =>
      expression env (RationalNestedResidualCode.vertices (NestedResidual.edges slot).2 j))))

noncomputable def residualFactory (r : NestedResidual) : Run (PreparedSegment 3 3) :=
  let env := residualEnvironment r
  join env (residualDescriptor env.value)

theorem residualFactory_value (r : NestedResidual) :
    (residualFactory r).value = PreparedSegment.ofLottery r.segmentLottery := by
  apply prepared_ext
  · apply table_ext
    intro slot
    simp only [residualFactory,join_value,residualDescriptor,assemble,arrayRun_read,expression_value,residualEnvironment_value,
      PreparedSegment.ofLottery,FixedArrayTable.read_ofFn,RealNestedResidualCode.weight_value,NestedResidual.segmentLottery]
  · apply table_ext
    intro slot
    apply table_ext
    intro j
    simp only [residualFactory,join_value,residualDescriptor,assemble,arrayRun_read,expression_value,residualEnvironment_value,
      PreparedSegment.ofLottery,FixedArrayTable.read_ofFn,RealNestedResidualCode.vertex_value,NestedResidual.segmentLottery]
  · apply table_ext
    intro slot
    apply table_ext
    intro j
    simp only [residualFactory,join_value,residualDescriptor,assemble,arrayRun_read,expression_value,residualEnvironment_value,
      PreparedSegment.ofLottery,FixedArrayTable.read_ofFn,RealNestedResidualCode.vertex_value,NestedResidual.segmentLottery]

theorem residualDescriptor_cost (env : FixedArrayTable 5 ℝ) : (residualDescriptor env).cost ≤ 1480 := by
  have hw := arrayRun_bound 3 256 (fun slot => expression env (RationalNestedResidualCode.weights slot))
    (fun slot => (expression_cost env _).trans (Nat.mul_le_mul_left 2 (RationalNestedResidualCode.weight_operationBound slot)))
  have hv : ∀ vertex : Fin 3, (arrayRun 3 (fun j => expression env (RationalNestedResidualCode.vertices vertex j))).cost ≤ 104 :=
    fun vertex => arrayRun_bound 3 32 _ (fun j => (expression_cost env _).trans
      (Nat.mul_le_mul_left 2 (RationalNestedResidualCode.vertex_operationBound vertex j)))
  have hP := arrayRun_bound 3 104 (fun slot => arrayRun 3 (fun j => expression env
    (RationalNestedResidualCode.vertices (NestedResidual.edges slot).1 j))) (fun slot => hv _)
  have hQ := arrayRun_bound 3 104 (fun slot => arrayRun 3 (fun j => expression env
    (RationalNestedResidualCode.vertices (NestedResidual.edges slot).2 j))) (fun slot => hv _)
  unfold residualDescriptor
  rw [assemble_cost]
  omega

theorem residualFactory_cost (r : NestedResidual) : (residualFactory r).cost ≤ 1500 := by
  have he := residualEnvironment_cost r
  have hd := residualDescriptor_cost (residualEnvironment r).value
  unfold residualFactory
  rw [join_cost]
  omega

noncomputable def residualDraw (r : NestedResidual) (seed : Fin 10 → ℝ) : Run (FixedArrayTable 3 ℝ) :=
  let prepared := residualFactory r
  let result := draw prepared.value 0 (RealUniformInputs.dropInputs 3 7 seed)
  join prepared (join (⟨(),[.control,.control,.control]⟩ : Run Unit) result)

theorem residualDraw_value (r : NestedResidual) (seed : Fin 10 → ℝ) :
    (residualDraw r seed).value.read = r.realSample seed := by
  unfold residualDraw
  dsimp only
  simp only [join_value]
  rw [residualFactory_value,draw_value]
  rw [r.realSample_refines]

theorem residualDraw_cost (r : NestedResidual) (seed : Fin 10 → ℝ) : (residualDraw r seed).cost ≤ 1600 := by
  have hf := residualFactory_cost r
  have hd : (draw (n := 3) (k := 3) (residualFactory r).value 0
      (RealUniformInputs.dropInputs 3 7 seed)).cost ≤ 94 :=
    draw_cost (n := 3) (k := 3) (residualFactory r).value 0 (RealUniformInputs.dropInputs 3 7 seed)
  unfold residualDraw
  rw [join_cost,join_cost]
  have hc : (⟨(),[Operation.control,.control,.control]⟩ : Run Unit).cost = 3 := rfl
  rw [hc]
  omega

noncomputable def copyRow {n : ℕ} (fields : Fin n → ℝ) : Run (FixedArrayTable n ℝ) :=
  arrayRun n (fun j => ⟨fields j,[.load j.val (fields j)]⟩)

@[simp] theorem copyRow_read {n : ℕ} (fields : Fin n → ℝ) : (copyRow fields).value.read = fields := by
  funext j
  simp [copyRow,arrayRun_read]

theorem copyRow_cost {n : ℕ} (fields : Fin n → ℝ) : (copyRow fields).cost = 3 * n + 2 := by
  unfold copyRow
  rw [arrayRun_cost]
  simp [Run.cost,Operation.cost]
  omega

noncomputable def shift (x : ℝ) (row : FixedArrayTable 3 ℝ) : Run (FixedArrayTable 3 ℝ) :=
  arrayRun 3 (fun j =>
    let cell := loadReal row j
    if j = 2 then join cell (arithmetic .add cell.value x) else cell)

theorem shift_value (x : ℝ) (row : FixedArrayTable 3 ℝ) :
    (shift x row).value.read = shiftThird x row.read := by
  funext j
  fin_cases j <;> simp [shift,arrayRun_read,join,loadReal,arithmetic,Operation.realValue,RealArithmeticOp.apply,shiftThird]

theorem shift_cost (x : ℝ) (row : FixedArrayTable 3 ℝ) : (shift x row).cost ≤ 14 := by
  apply arrayRun_bound 3 2
  intro j
  split_ifs
  · rw [join_cost]
    simp [loadReal,arithmetic,Run.cost,Operation.cost]
  · simp [loadReal,Run.cost,Operation.cost]

noncomputable def firstPositive (i : NestedInput) (s : ℝ) (seed : Fin 9 → ℝ) : Run (FixedArrayTable 3 ℝ) :=
  let env := nestedEnvironment i s
  let params := firstParameters env.value
  let prepared := geometryFactory params.value
  let result := draw prepared.value 0 seed
  join env (join params (join prepared (join result (shift s result.value))))

theorem firstPositive_value (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (hp : 0 < i.conditionalProbability s) (seed : Fin 9 → ℝ) :
    (firstPositive i s seed).value.read = i.realFirstPositive htv s hs hp seed := by
  simp only [firstPositive,join_value,shift_value,firstParameters_value i htv s hs hp,
    geometryFactory_value,draw_value]
  exact (i.realFirstPositive_refines htv s hs hp seed).symm

theorem firstPositive_cost (i : NestedInput) (s : ℝ) (seed : Fin 9 → ℝ) :
    (firstPositive i s seed).cost ≤ 6500 := by
  have he := nestedEnvironment_cost i s
  have hp := firstParameters_cost (nestedEnvironment i s).value
  have hf := geometryFactory_cost (firstParameters (nestedEnvironment i s).value).value
  have hd := draw_cost (geometryFactory (firstParameters (nestedEnvironment i s).value).value).value 0 seed
  have hs := shift_cost s (draw (geometryFactory (firstParameters (nestedEnvironment i s).value).value).value 0 seed).value
  unfold firstPositive
  rw [join_cost,join_cost,join_cost,join_cost]
  omega

noncomputable def firstZero (i : NestedInput) (s : ℝ) (seed : Fin 9 → ℝ) : Run (FixedArrayTable 3 ℝ) :=
  let P := copyRow ![0,i.d,s]
  let Q := copyRow ![i.a,0,s]
  let t := uniform (seed 0)
  join P (join Q (join t (point P.value Q.value t.value)))

theorem firstZero_value (i : NestedInput) (s : ℝ) (seed : Fin 9 → ℝ) :
    (firstZero i s seed).value.read = i.realFirstZero s seed := by
  simp only [firstZero,join_value,point_value,copyRow_read,uniform,Operation.realValue]
  exact (i.realFirstZero_refines s seed).symm

theorem firstZero_cost (i : NestedInput) (s : ℝ) (seed : Fin 9 → ℝ) :
    (firstZero i s seed).cost ≤ 60 := by
  unfold firstZero
  rw [join_cost,join_cost,join_cost,copyRow_cost,copyRow_cost,point_cost]
  simp [uniform,Run.cost,Operation.cost]

noncomputable def compareLt (x y : ℝ) : Run Bool :=
  ⟨decide (x < y),[.strictComparison x y]⟩

noncomputable def firstConditional (i : NestedInput) (_htv : i.t ≤ i.v) (s : ℝ)
    (seed : Fin 9 → ℝ) : Run (FixedArrayTable 3 ℝ) :=
  let env := nestedEnvironment i s
  let probability := expression env.value RationalNestedParametersCode.conditional
  let lower := compareLe 0 s
  let upper := compareLe s i.t
  let positive := compareLt 0 probability.value
  let result := if lower.value && upper.value && positive.value then firstPositive i s seed else firstZero i s seed
  join env (join probability (join lower (join upper (join positive
    (join (⟨(),[.control,.control,.control]⟩ : Run Unit) result)))))

theorem firstConditional_value (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ) (seed : Fin 9 → ℝ) :
    (firstConditional i htv s seed).value.read = i.realFirstConditional htv s seed := by
  have hp : (expression (nestedEnvironment i s).value RationalNestedParametersCode.conditional).value =
      i.conditionalProbability s := by
    rw [expression_value,nestedEnvironment_value,RealNestedParametersCode.conditional_value]
  unfold firstConditional
  simp only [join_value,hp,compareLe,compareLt,Bool.and_eq_true,decide_eq_true_eq]
  rw [i.realFirstConditional_refines htv]
  by_cases hs : s ∈ i.positiveParameters
  · have hg : 0 ≤ s ∧ s ≤ i.t ∧ 0 < i.conditionalProbability s := ⟨hs.1.1,hs.1.2,hs.2⟩
    simp only [hg.1,hg.2.1,hg.2.2,and_self,ite_true,dite_eq_left hs]
    exact firstPositive_value i htv s hs.1 hs.2 seed
  · have hg : ¬ ((0 ≤ s ∧ s ≤ i.t) ∧ 0 < i.conditionalProbability s) := hs
    simp only [hg,ite_false,dite_eq_right hs]
    exact firstZero_value i s seed

theorem firstConditional_cost (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ) (seed : Fin 9 → ℝ) :
    (firstConditional i htv s seed).cost ≤ 6900 := by
  have he := nestedEnvironment_cost i s
  have hp : (expression (nestedEnvironment i s).value RationalNestedParametersCode.conditional).cost ≤ 256 := by
    apply (expression_cost _ _).trans
    exact Nat.mul_le_mul_left 2 (RationalNestedParametersCode.scalar_operationBound 1)
  have hYes := firstPositive_cost i s seed
  have hNo := firstZero_cost i s seed
  unfold firstConditional
  rw [join_cost,join_cost,join_cost,join_cost,join_cost,join_cost]
  have hL : (compareLe 0 s).cost = 1 := rfl
  have hU : (compareLe s i.t).cost = 1 := rfl
  have hP : (compareLt 0 (expression (nestedEnvironment i s).value RationalNestedParametersCode.conditional).value).cost = 1 := rfl
  have hC : (⟨(),[Operation.control,.control,.control]⟩ : Run Unit).cost = 3 := rfl
  rw [hL,hU,hP,hC]
  split <;> omega

noncomputable def firstDraw (i : NestedInput) (htv : i.t ≤ i.v) (seed : Fin 10 → ℝ) : Run (FixedArrayTable 3 ℝ) :=
  let u := uniform (seed 0)
  let env := nestedEnvironment i u.value
  let location := expression env.value RationalNestedParametersCode.location
  join u (join env (join location (firstConditional i htv location.value (Fin.tail seed))))

theorem firstDraw_value (i : NestedInput) (htv : i.t ≤ i.v) (seed : Fin 10 → ℝ) :
    (firstDraw i htv seed).value.read = i.realFirstSample htv seed := by
  simp only [firstDraw,join_value,firstConditional_value,expression_value,nestedEnvironment_value,
    uniform,Operation.realValue,RealNestedParametersCode.location_value]
  exact (i.realFirstSample_refines htv seed).symm

theorem firstDraw_cost (i : NestedInput) (htv : i.t ≤ i.v) (seed : Fin 10 → ℝ) :
    (firstDraw i htv seed).cost ≤ 7200 := by
  have he := nestedEnvironment_cost i (seed 0)
  have hl : (expression (nestedEnvironment i (seed 0)).value RationalNestedParametersCode.location).cost ≤ 256 :=
    (expression_cost _ _).trans (Nat.mul_le_mul_left 2 (RationalNestedParametersCode.scalar_operationBound 0))
  have hd := firstConditional_cost i htv
    (expression (nestedEnvironment i (seed 0)).value RationalNestedParametersCode.location).value (Fin.tail seed)
  unfold firstDraw
  rw [join_cost,join_cost,join_cost]
  have hu : (uniform (seed 0)).cost = 1 := rfl
  rw [hu]
  simp only [uniform,Operation.realValue]
  omega

noncomputable def familyInput (i : NestedInput) (x : ℝ) (hx : 0 < x) (hxuv : x < i.u + i.v) : Run NestedInput :=
  let env := nestedEnvironment i x
  let probability := expression env.value RationalNestedParametersCode.familyProbability
  have hq : probability.value = i.familyProbability x := by
    rw [expression_value,nestedEnvironment_value,RealNestedParametersCode.familyProbability_value]
  let old := i.atLength x hx hxuv
  let produced : NestedInput := {old with
    q := probability.value
    q_pos := by rw [hq]; exact old.q_pos
    q_lt := by rw [hq]; exact old.q_lt
    balance := by rw [hq]; exact old.balance}
  join env (join probability
    ⟨produced,[.load 0 i.M,.load 1 i.a,.load 2 i.d,.load 3 i.c,.load 4 x,.load 5 probability.value,
      .storeCell 0,.storeCell 1,.storeCell 2,.storeCell 3,.storeCell 4,.storeCell 5,.control]⟩)

theorem familyInput_value (i : NestedInput) (x : ℝ) (hx : 0 < x) (hxuv : x < i.u + i.v) :
    (familyInput i x hx hxuv).value = i.atLength x hx hxuv := by
  simp only [familyInput,join_value,expression_value,nestedEnvironment_value,
    RealNestedParametersCode.familyProbability_value]
  rfl

theorem familyInput_cost (i : NestedInput) (x : ℝ) (hx : 0 < x) (hxuv : x < i.u + i.v) :
    (familyInput i x hx hxuv).cost ≤ 300 := by
  have he := nestedEnvironment_cost i x
  have hp : (expression (nestedEnvironment i x).value RationalNestedParametersCode.familyProbability).cost ≤ 256 :=
    (expression_cost _ _).trans (Nat.mul_le_mul_left 2 (RationalNestedParametersCode.scalar_operationBound 2))
  unfold familyInput
  rw [join_cost,join_cost]
  change (nestedEnvironment i x).cost + ((expression _ _).cost + 13) ≤ _
  omega

noncomputable def familyDraw (i : NestedInput) (x : ℝ) (hx : 0 < x) (hxv : x ≤ i.v)
    (seed : Fin 10 → ℝ) : Run (FixedArrayTable 3 ℝ) :=
  let prepared := familyInput i x hx (by linarith [i.lengths.2.2.1])
  have ht : prepared.value.t ≤ prepared.value.v := by rw [familyInput_value]; exact hxv
  join prepared (firstDraw prepared.value ht seed)

theorem familyDraw_value (i : NestedInput) (x : ℝ) (hx : 0 < x) (hxv : x ≤ i.v) (seed : Fin 10 → ℝ) :
    (familyDraw i x hx hxv seed).value.read = i.realFamilyFirstSample x hx hxv seed := by
  simp only [familyDraw,join_value,firstDraw_value,familyInput_value]
  rw [i.realFamilyFirstSample_refines]

theorem familyDraw_cost (i : NestedInput) (x : ℝ) (hx : 0 < x) (hxv : x ≤ i.v) (seed : Fin 10 → ℝ) :
    (familyDraw i x hx hxv seed).cost ≤ 7500 := by
  have hi := familyInput_cost i x hx (by linarith [i.lengths.2.2.1])
  unfold familyDraw
  rw [join_cost]
  have hd := firstDraw_cost (familyInput i x hx (by linarith [i.lengths.2.2.1])).value
    (by rw [familyInput_value]; exact hxv) seed
  omega

noncomputable def storedThree (old : ThreeInput) (env : FixedArrayTable 5 ℝ)
    (h : env = RealThreeInputPreparationCode.environment old) : ThreeInput where
  B := env.read 0
  a := env.read 1
  d := env.read 2
  c := env.read 3
  p := env.read 4
  B_pos := by simpa [h,RealThreeInputPreparationCode.environment,FixedArrayTable.read_ofFn] using old.B_pos
  a_pos := by simpa [h,RealThreeInputPreparationCode.environment,FixedArrayTable.read_ofFn] using old.a_pos
  d_pos := by simpa [h,RealThreeInputPreparationCode.environment,FixedArrayTable.read_ofFn] using old.d_pos
  c_pos := by simpa [h,RealThreeInputPreparationCode.environment,FixedArrayTable.read_ofFn] using old.c_pos
  p_pos := by simpa [h,RealThreeInputPreparationCode.environment,FixedArrayTable.read_ofFn] using old.p_pos
  a_le := by simpa [h,RealThreeInputPreparationCode.environment,FixedArrayTable.read_ofFn] using old.a_le
  d_le := by simpa [h,RealThreeInputPreparationCode.environment,FixedArrayTable.read_ofFn] using old.d_le
  c_le := by simpa [h,RealThreeInputPreparationCode.environment,FixedArrayTable.read_ofFn] using old.c_le
  p_le := by simpa [h,RealThreeInputPreparationCode.environment,FixedArrayTable.read_ofFn] using old.p_le
  ordered := by simpa [h,RealThreeInputPreparationCode.environment,FixedArrayTable.read_ofFn] using old.ordered
  balance := by simpa [h,RealThreeInputPreparationCode.environment,FixedArrayTable.read_ofFn] using old.balance

theorem storedThree_value (old : ThreeInput) (env : FixedArrayTable 5 ℝ)
    (h : env = RealThreeInputPreparationCode.environment old) : storedThree old env h = old := by
  cases h
  rfl

noncomputable def secondUniformFields (env : FixedArrayTable 7 ℝ) : Run (FixedArrayTable 5 ℝ) :=
  arrayRun 5 (fun j => expression env (RationalSecondUniformCode.programs j))

theorem secondUniformFields_value (i : NestedInput) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t) :
    (secondUniformFields (nestedEnvironment i 0).value).value =
      RealThreeInputPreparationCode.environment (i.secondUniformInput htu hTt) := by
  apply table_ext
  intro j
  simp only [secondUniformFields,arrayRun_read,expression_value,nestedEnvironment_value]
  exact RealSecondUniformPreparationCode.field_value i htu hTt j

theorem secondUniformFields_cost (env : FixedArrayTable 7 ℝ) : (secondUniformFields env).cost ≤ 1292 :=
  arrayRun_bound 5 256 _ (fun j => (expression_cost env _).trans
    (Nat.mul_le_mul_left 2 (RationalSecondUniformCode.operations j)))

noncomputable def secondUniformDraw (i : NestedInput) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t)
    (seed : Fin 10 → ℝ) : Run (FixedArrayTable 3 ℝ) :=
  let env := nestedEnvironment i 0
  let fields := secondUniformFields env.value
  let produced := storedThree (i.secondUniformInput htu hTt) fields.value (secondUniformFields_value i htu hTt)
  let mirror := expression env.value RationalNestedParametersCode.mirror
  let result := orderedDraw produced (Fin.tail seed)
  join env (join fields (join mirror (join result (shift mirror.value result.value))))

theorem secondUniformDraw_value (i : NestedInput) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t)
    (seed : Fin 10 → ℝ) : (secondUniformDraw i htu hTt seed).value.read =
      i.realSecondUniformSample htu hTt seed := by
  simp only [secondUniformDraw,join_value,shift_value,storedThree_value,orderedDraw_value,
    expression_value,nestedEnvironment_value,RealNestedParametersCode.mirror_value]
  exact (i.realSecondUniformSample_refines htu hTt seed).symm

theorem secondUniformDraw_cost (i : NestedInput) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t)
    (seed : Fin 10 → ℝ) : (secondUniformDraw i htu hTt seed).cost ≤ 8600 := by
  have he := nestedEnvironment_cost i 0
  have hf := secondUniformFields_cost (nestedEnvironment i 0).value
  have hm : (expression (nestedEnvironment i 0).value RationalNestedParametersCode.mirror).cost ≤ 256 :=
    (expression_cost _ _).trans (Nat.mul_le_mul_left 2 (RationalNestedParametersCode.scalar_operationBound 3))
  unfold secondUniformDraw
  rw [join_cost,join_cost,join_cost,join_cost]
  have hd := orderedDraw_cost (storedThree (i.secondUniformInput htu hTt)
    (secondUniformFields (nestedEnvironment i 0).value).value (secondUniformFields_value i htu hTt)) (Fin.tail seed)
  have hs := shift_cost (expression (nestedEnvironment i 0).value RationalNestedParametersCode.mirror).value
    (orderedDraw (storedThree (i.secondUniformInput htu hTt)
      (secondUniformFields (nestedEnvironment i 0).value).value (secondUniformFields_value i htu hTt)) (Fin.tail seed)).value
  omega

noncomputable def residualFields (env : FixedArrayTable 7 ℝ) : Run (FixedArrayTable 5 ℝ) :=
  arrayRun 5 (fun j => expression env (RationalNestedResidualPreparationCode.programs j))

theorem residualFields_value (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) :
    (residualFields (nestedEnvironment i 0).value).value =
      RealNestedResidualCode.environment (i.residualInput hvt htu) := by
  apply table_ext
  intro j
  simp only [residualFields,arrayRun_read,expression_value,nestedEnvironment_value]
  exact RealNestedResidualPreparationCode.field_value i hvt htu j

theorem residualFields_cost (env : FixedArrayTable 7 ℝ) : (residualFields env).cost ≤ 172 :=
  arrayRun_bound 5 32 _ (fun j => (expression_cost env _).trans
    (Nat.mul_le_mul_left 2 (RationalNestedResidualPreparationCode.operations j)))

theorem residualDescriptor_value (r : NestedResidual) :
    (residualDescriptor (RealNestedResidualCode.environment r)).value = PreparedSegment.ofLottery r.segmentLottery := by
  have h := residualFactory_value r
  simpa only [residualFactory,join_value,residualEnvironment_value] using h

noncomputable def preparedResidualDraw (i : NestedInput) (seed : Fin 10 → ℝ) : Run (FixedArrayTable 3 ℝ) :=
  let env := nestedEnvironment i 0
  let fields := residualFields env.value
  let prepared := residualDescriptor fields.value
  let result := draw prepared.value 0 (RealUniformInputs.dropInputs 3 7 seed)
  join env (join fields (join prepared result))

theorem preparedResidualDraw_value (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u)
    (seed : Fin 10 → ℝ) : (preparedResidualDraw i seed).value.read = (i.residualInput hvt htu).realSample seed := by
  simp only [preparedResidualDraw,join_value,residualFields_value i hvt htu,residualDescriptor_value,draw_value]
  rw [(i.residualInput hvt htu).realSample_refines]

theorem preparedResidualDraw_cost (i : NestedInput) (seed : Fin 10 → ℝ) :
    (preparedResidualDraw i seed).cost ≤ 1800 := by
  have he := nestedEnvironment_cost i 0
  have hf := residualFields_cost (nestedEnvironment i 0).value
  have hp := residualDescriptor_cost (residualFields (nestedEnvironment i 0).value).value
  have hd := draw_cost (residualDescriptor (residualFields (nestedEnvironment i 0).value).value).value 0
    (RealUniformInputs.dropInputs 3 7 seed)
  unfold preparedResidualDraw
  rw [join_cost,join_cost,join_cost]
  omega

noncomputable def binaryChoice {n C : ℕ} (p : ℝ)
    (upper lower : (Fin C → ℝ) → Run (FixedArrayTable n ℝ)) (seed : Fin (C + 1) → ℝ) : Run (FixedArrayTable n ℝ) :=
  let u := uniform (seed 0)
  let choice := compareLe u.value p
  let result := if choice.value then upper (Fin.tail seed) else lower (Fin.tail seed)
  join u (join choice (join (⟨(),[.control]⟩ : Run Unit) result))

theorem binaryChoice_value {n C : ℕ} (p : ℝ)
    (upper lower : (Fin C → ℝ) → Run (FixedArrayTable n ℝ)) (seed : Fin (C + 1) → ℝ) :
    (binaryChoice p upper lower seed).value.read =
      realBinarySample p (fun s => (upper s).value.read) (fun s => (lower s).value.read) seed := by
  by_cases h : seed 0 ≤ p <;>
    simp [binaryChoice,join_value,uniform,Operation.realValue,compareLe,realBinarySample,h]

theorem binaryChoice_cost {n C B : ℕ} (p : ℝ)
    (upper lower : (Fin C → ℝ) → Run (FixedArrayTable n ℝ)) (seed : Fin (C + 1) → ℝ)
    (hU : (upper (Fin.tail seed)).cost ≤ B) (hL : (lower (Fin.tail seed)).cost ≤ B) :
    (binaryChoice p upper lower seed).cost ≤ B + 3 := by
  unfold binaryChoice
  rw [join_cost,join_cost,join_cost]
  have hu : (uniform (seed 0)).cost = 1 := rfl
  have hc : (compareLe (uniform (seed 0)).value p).cost = 1 := rfl
  have hb : (⟨(),[Operation.control]⟩ : Run Unit).cost = 1 := rfl
  rw [hu,hc,hb]
  split <;> omega

noncomputable def secondDraw (i : NestedInput) (htu : i.u ≤ i.t) (seed : Fin 11 → ℝ) : Run (FixedArrayTable 3 ℝ) :=
  let env := nestedEnvironment i 0
  let mirror := expression env.value RationalNestedParametersCode.mirror
  have hMirror : mirror.value = i.mirrorLength := by
    rw [expression_value,nestedEnvironment_value,RealNestedParametersCode.mirror_value]
  have hPos : 0 < mirror.value := by rw [hMirror]; exact (i.mirrorLength_bounds htu).1
  have hV : mirror.value ≤ i.v := by rw [hMirror]; exact (i.mirrorLength_bounds htu).2.1
  let compared := compareLt mirror.value i.t
  let result := if hTt : mirror.value < i.t then
    let alpha := expression env.value RationalNestedParametersCode.secondAlpha
    join alpha (binaryChoice alpha.value (familyDraw i mirror.value hPos hV)
      (secondUniformDraw i htu (by simpa only [hMirror] using hTt)) seed)
  else familyDraw i mirror.value hPos hV (Fin.tail seed)
  join env (join mirror (join compared (join (⟨(),[.control]⟩ : Run Unit) result)))

theorem secondDraw_value (i : NestedInput) (htu : i.u ≤ i.t) (seed : Fin 11 → ℝ) :
    (secondDraw i htu seed).value.read = i.realSecondSample htu seed := by
  rw [i.realSecondSample_refines htu]
  simp only [secondDraw,join_value,expression_value,nestedEnvironment_value,
    RealNestedParametersCode.mirror_value,RealNestedParametersCode.secondAlpha_value]
  split_ifs with hTt
  · simp only [join_value]
    rw [binaryChoice_value]
    congr 1 <;> funext s
    · rw [familyDraw_value]
      apply i.realFamilyFirstSample_length_congr
      rw [expression_value,nestedEnvironment_value,RealNestedParametersCode.mirror_value]
    · exact secondUniformDraw_value i htu hTt s
  · rw [familyDraw_value]

theorem secondDraw_cost (i : NestedInput) (htu : i.u ≤ i.t) (seed : Fin 11 → ℝ) :
    (secondDraw i htu seed).cost ≤ 9300 := by
  have he := nestedEnvironment_cost i 0
  have hm : (expression (nestedEnvironment i 0).value RationalNestedParametersCode.mirror).cost ≤ 256 :=
    (expression_cost _ _).trans (Nat.mul_le_mul_left 2 (RationalNestedParametersCode.scalar_operationBound 3))
  have ha : (expression (nestedEnvironment i 0).value RationalNestedParametersCode.secondAlpha).cost ≤ 256 :=
    (expression_cost _ _).trans (Nat.mul_le_mul_left 2 (RationalNestedParametersCode.scalar_operationBound 4))
  have hMirror : (expression (nestedEnvironment i 0).value RationalNestedParametersCode.mirror).value = i.mirrorLength := by
    rw [expression_value,nestedEnvironment_value,RealNestedParametersCode.mirror_value]
  have hPos : 0 < (expression (nestedEnvironment i 0).value RationalNestedParametersCode.mirror).value := by
    rw [hMirror]; exact (i.mirrorLength_bounds htu).1
  have hV : (expression (nestedEnvironment i 0).value RationalNestedParametersCode.mirror).value ≤ i.v := by
    rw [hMirror]; exact (i.mirrorLength_bounds htu).2.1
  unfold secondDraw
  rw [join_cost,join_cost,join_cost,join_cost]
  have hc : (compareLt (expression (nestedEnvironment i 0).value RationalNestedParametersCode.mirror).value i.t).cost = 1 := rfl
  have hb : (⟨(),[Operation.control]⟩ : Run Unit).cost = 1 := rfl
  rw [hc,hb]
  split
  · rename_i hTt
    rw [join_cost]
    have hOriginal : i.mirrorLength < i.t := by simpa only [hMirror] using hTt
    have hU := familyDraw_cost i
      (expression (nestedEnvironment i 0).value RationalNestedParametersCode.mirror).value hPos hV (Fin.tail seed)
    have hL := secondUniformDraw_cost i htu hOriginal (Fin.tail seed)
    have hd := binaryChoice_cost
      (expression (nestedEnvironment i 0).value RationalNestedParametersCode.secondAlpha).value
      (familyDraw i (expression (nestedEnvironment i 0).value RationalNestedParametersCode.mirror).value hPos hV)
      (secondUniformDraw i htu hOriginal) seed (hU.trans (by decide : 7500 ≤ 8600)) hL
    omega
  · have hd := familyDraw_cost i
      (expression (nestedEnvironment i 0).value RationalNestedParametersCode.mirror).value hPos hV (Fin.tail seed)
    omega

noncomputable def thirdDraw (i : NestedInput) (_hvt : i.v < i.t) (_htu : i.t < i.u)
    (seed : Fin 11 → ℝ) : Run (FixedArrayTable 3 ℝ) :=
  let env := nestedEnvironment i 0
  let v := expression env.value RationalNestedParametersCode.V
  have hvEq : v.value = i.v := by rw [expression_value,nestedEnvironment_value,RealNestedParametersCode.V_value]
  let compared := compareLt 0 v.value
  let result := if hv : 0 < v.value then
    let alpha := expression env.value RationalNestedParametersCode.thirdAlpha
    join alpha (binaryChoice alpha.value (familyDraw i v.value hv (by rw [hvEq]))
      (preparedResidualDraw i) seed)
  else preparedResidualDraw i (Fin.tail seed)
  join env (join v (join compared (join (⟨(),[.control]⟩ : Run Unit) result)))

theorem thirdDraw_value (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (seed : Fin 11 → ℝ) :
    (thirdDraw i hvt htu seed).value.read = i.realThirdSample hvt htu seed := by
  rw [i.realThirdSample_refines hvt htu]
  simp only [thirdDraw,join_value,expression_value,nestedEnvironment_value,
    RealNestedParametersCode.V_value,RealNestedParametersCode.thirdAlpha_value]
  split_ifs with hv
  · simp only [join_value]
    rw [binaryChoice_value]
    congr 1 <;> funext s
    · rw [familyDraw_value]
      apply i.realFamilyFirstSample_length_congr
      rw [expression_value,nestedEnvironment_value,RealNestedParametersCode.V_value]
    · exact preparedResidualDraw_value i hvt htu s
  · exact preparedResidualDraw_value i hvt htu (Fin.tail seed)

theorem thirdDraw_cost (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (seed : Fin 11 → ℝ) :
    (thirdDraw i hvt htu seed).cost ≤ 7900 := by
  have he := nestedEnvironment_cost i 0
  have hv : (expression (nestedEnvironment i 0).value RationalNestedParametersCode.V).cost ≤ 6 :=
    (expression_cost _ _).trans (by decide)
  have hUeq : (expression (nestedEnvironment i 0).value RationalNestedParametersCode.U).value = i.u := by
    rw [expression_value,nestedEnvironment_value,RealNestedParametersCode.U_value]
  have hVeq : (expression (nestedEnvironment i 0).value RationalNestedParametersCode.V).value = i.v := by
    rw [expression_value,nestedEnvironment_value,RealNestedParametersCode.V_value]
  have ha : (expression (nestedEnvironment i 0).value RationalNestedParametersCode.thirdAlpha).cost ≤ 256 :=
    (expression_cost _ _).trans (Nat.mul_le_mul_left 2 (RationalNestedParametersCode.scalar_operationBound 5))
  have hVeq : (expression (nestedEnvironment i 0).value RationalNestedParametersCode.V).value = i.v := by
    rw [expression_value,nestedEnvironment_value,RealNestedParametersCode.V_value]
  have hVle : (expression (nestedEnvironment i 0).value RationalNestedParametersCode.V).value ≤ i.v := by rw [hVeq]
  unfold thirdDraw
  rw [join_cost,join_cost,join_cost,join_cost]
  have hc : (compareLt 0 (expression (nestedEnvironment i 0).value RationalNestedParametersCode.V).value).cost = 1 := rfl
  have hb : (⟨(),[Operation.control]⟩ : Run Unit).cost = 1 := rfl
  rw [hc,hb]
  split
  · rename_i hVpos
    rw [join_cost]
    have hU := familyDraw_cost i (expression (nestedEnvironment i 0).value RationalNestedParametersCode.V).value hVpos hVle (Fin.tail seed)
    have hL := preparedResidualDraw_cost i (Fin.tail seed)
    have hd := binaryChoice_cost (expression (nestedEnvironment i 0).value RationalNestedParametersCode.thirdAlpha).value
      (familyDraw i (expression (nestedEnvironment i 0).value RationalNestedParametersCode.V).value hVpos hVle) (preparedResidualDraw i) seed
      hU (hL.trans (by decide : 1800 ≤ 7500))
    omega
  · have hd := preparedResidualDraw_cost i (Fin.tail seed)
    omega

noncomputable def nestedDraw (i : NestedInput) (seed : Fin 11 → ℝ) : Run (FixedArrayTable 3 ℝ) :=
  let env := nestedEnvironment i 0
  let u := expression env.value RationalNestedParametersCode.U
  let v := expression env.value RationalNestedParametersCode.V
  have hU : u.value = i.u := by rw [expression_value,nestedEnvironment_value,RealNestedParametersCode.U_value]
  have hV : v.value = i.v := by rw [expression_value,nestedEnvironment_value,RealNestedParametersCode.V_value]
  let first := compareLe i.t v.value
  let second := compareLe u.value i.t
  let result := if htv : i.t ≤ v.value then firstDraw i (by simpa only [hV] using htv) (Fin.tail seed) else
    if htu : u.value ≤ i.t then secondDraw i (by simpa only [hU] using htu) seed else
      thirdDraw i (by rw [← hV]; exact lt_of_not_ge htv) (by rw [← hU]; exact lt_of_not_ge htu) seed
  join env (join u (join v (join first (join second (join (⟨(),[.control,.control]⟩ : Run Unit) result)))))

theorem nestedDraw_value (i : NestedInput) (seed : Fin 11 → ℝ) :
    (nestedDraw i seed).value.read = i.realSample seed := by
  simp only [nestedDraw,join_value,expression_value,nestedEnvironment_value,RealNestedParametersCode.U_value,
    RealNestedParametersCode.V_value,NestedInput.realSample]
  split_ifs with htv htu
  · exact firstDraw_value i htv (Fin.tail seed)
  · exact secondDraw_value i htu seed
  · exact thirdDraw_value i _ _ seed

theorem nestedDraw_cost (i : NestedInput) (seed : Fin 11 → ℝ) : (nestedDraw i seed).cost ≤ 9400 := by
  have he := nestedEnvironment_cost i 0
  have hu : (expression (nestedEnvironment i 0).value RationalNestedParametersCode.U).cost ≤ 6 :=
    (expression_cost _ _).trans (by decide)
  have hv : (expression (nestedEnvironment i 0).value RationalNestedParametersCode.V).cost ≤ 6 :=
    (expression_cost _ _).trans (by decide)
  have hUeq : (expression (nestedEnvironment i 0).value RationalNestedParametersCode.U).value = i.u := by
    rw [expression_value,nestedEnvironment_value,RealNestedParametersCode.U_value]
  have hVeq : (expression (nestedEnvironment i 0).value RationalNestedParametersCode.V).value = i.v := by
    rw [expression_value,nestedEnvironment_value,RealNestedParametersCode.V_value]
  unfold nestedDraw
  rw [join_cost,join_cost,join_cost,join_cost,join_cost,join_cost]
  have hFirst : (compareLe i.t (expression (nestedEnvironment i 0).value RationalNestedParametersCode.V).value).cost = 1 := rfl
  have hSecond : (compareLe (expression (nestedEnvironment i 0).value RationalNestedParametersCode.U).value i.t).cost = 1 := rfl
  have hControl : (⟨(),[Operation.control,.control]⟩ : Run Unit).cost = 2 := rfl
  rw [hFirst,hSecond,hControl]
  split
  · rename_i htv
    have hd := firstDraw_cost i (by simpa only [hVeq] using htv) (Fin.tail seed)
    omega
  · rename_i htv
    split
    · rename_i htu
      have hd := secondDraw_cost i (by simpa only [hUeq] using htu) seed
      omega
    · rename_i htu
      have hd := thirdDraw_cost i (by rw [← hVeq]; exact lt_of_not_ge htv)
        (by rw [← hUeq]; exact lt_of_not_ge htu) seed
      omega

theorem nestedDraw_law (i : NestedInput) :
    Measure.map (fun seed => (nestedDraw i seed).value.read)
      (RealUniformInputs.law 11 : Measure (Fin 11 → ℝ)) = (i.couplingLaw : Measure (Allocation 3)) := by
  have h : (fun seed => (nestedDraw i seed).value.read) = i.realSample := funext (nestedDraw_value i)
  rw [h]
  exact i.realSample_law

theorem nestedDraw_fullBudget (i : NestedInput) (seed : Fin 11 → ℝ)
    (h : ∀ j, 0 ≤ seed j ∧ seed j ≤ 1) : FullBudget i.M (nestedDraw i seed).value.read := by
  rw [nestedDraw_value]
  exact i.realSample_fullBudget seed h

noncomputable def swapRow (row : FixedArrayTable 3 ℝ) : Run (FixedArrayTable 3 ℝ) :=
  arrayRun 3 (fun j => loadReal row (swapIndex j))

theorem swapRow_value (row : FixedArrayTable 3 ℝ) : (swapRow row).value.read = swapFirst row.read := by
  funext j
  fin_cases j <;> simp [swapRow,arrayRun_read,loadReal,Operation.realValue,swapIndex,swapFirst]

theorem swapRow_cost (row : FixedArrayTable 3 ℝ) : (swapRow row).cost ≤ 11 :=
  arrayRun_bound 3 1 _ (fun _ => by rfl)

theorem mapped_realSampleFlat {n m k : ℕ} (l : SegmentLottery n k) (f : AffineAllocation n m)
    (fallback : Fin k) (seed : Fin ((k - 1) + 1) → ℝ) :
    (l.mapped f).realSampleFlat fallback seed = f.value (l.realSampleFlat fallback seed) := by
  rw [SegmentLottery.realSampleFlat_refines,SegmentLottery.realSampleFlat_refines]
  change segmentPoint (f.value _) (f.value _) _ = f.value (segmentPoint _ _ _)
  exact (f.onSegment _ _ _).symm

noncomputable def orderedThreeInput (i : ThreeSpec) : Run ThreeInput :=
  let a := arithmetic .minimum i.a i.d
  let d := arithmetic .maximum i.a i.d
  let fields := copyRow ![i.B,a.value,d.value,i.c,i.p]
  have hFields : fields.value = RealThreeInputPreparationCode.environment i.orderedInput := by
    apply table_ext
    intro j
    simp [fields,a,d,copyRow,arrayRun_read,arithmetic,Operation.realValue,RealArithmeticOp.apply,
      RealThreeInputPreparationCode.environment,ThreeSpec.orderedInput,FixedArrayTable.read_ofFn]
  join a (join d (join fields ⟨storedThree i.orderedInput fields.value hFields,[]⟩))

theorem orderedThreeInput_value (i : ThreeSpec) : (orderedThreeInput i).value = i.orderedInput := by
  simp only [orderedThreeInput,join_value,storedThree_value]

theorem orderedThreeInput_cost (i : ThreeSpec) : (orderedThreeInput i).cost ≤ 30 := by
  unfold orderedThreeInput
  rw [join_cost,join_cost,join_cost,copyRow_cost]
  change 2 + (2 + (17 + 0)) ≤ 30
  decide

noncomputable def threeDraw (i : ThreeSpec) (seed : Fin 9 → ℝ) : Run (FixedArrayTable 3 ℝ) :=
  let prepared := orderedThreeInput i
  let result := orderedDraw prepared.value seed
  let compared := compareLe i.a i.d
  let restored := if compared.value then result else join result (swapRow result.value)
  join prepared (join compared (join (⟨(),[.control]⟩ : Run Unit) restored))

theorem threeDraw_value (i : ThreeSpec) (seed : Fin 9 → ℝ) :
    (threeDraw i seed).value.read = i.realSample seed := by
  rw [i.realSample_refines seed]
  simp only [threeDraw,join_value,orderedThreeInput_value,compareLe,decide_eq_true_eq]
  unfold ThreeSpec.segmentLottery
  by_cases h : i.a ≤ i.d
  · simp only [h,ite_true,orderedDraw_value]
  · simp only [h,ite_false,join_value,swapRow_value,orderedDraw_value,mapped_realSampleFlat]
    rfl

theorem threeDraw_cost (i : ThreeSpec) (seed : Fin 9 → ℝ) : (threeDraw i seed).cost ≤ 7100 := by
  have hp := orderedThreeInput_cost i
  have hd := orderedDraw_cost (orderedThreeInput i).value seed
  have hs := swapRow_cost (orderedDraw (orderedThreeInput i).value seed).value
  unfold threeDraw
  rw [join_cost,join_cost,join_cost]
  have hc : (compareLe i.a i.d).cost = 1 := rfl
  have hb : (⟨(),[Operation.control]⟩ : Run Unit).cost = 1 := rfl
  rw [hc,hb]
  split
  · omega
  · rw [join_cost]
    omega

theorem threeDraw_law (i : ThreeSpec) :
    Measure.map (fun seed => (threeDraw i seed).value.read)
      (RealUniformInputs.law 9 : Measure (Fin 9 → ℝ)) = (i.law : Measure (Allocation 3)) := by
  have h : (fun seed => (threeDraw i seed).value.read) = i.realSample := funext (threeDraw_value i)
  rw [h]
  exact i.realSample_law

theorem threeDraw_fullBudget (i : ThreeSpec) (seed : Fin 9 → ℝ) (h : 0 ≤ seed 0 ∧ seed 0 ≤ 1) :
    FullBudget i.B (threeDraw i seed).value.read := by
  rw [threeDraw_value]
  exact i.realSample_fullBudget seed h

noncomputable def nestedFields (i : NestedInput) : FixedArrayTable 6 ℝ := FixedArrayTable.ofFn ![i.M,i.a,i.d,i.c,i.t,i.q]

noncomputable def storedNested (old : NestedInput) (env : FixedArrayTable 6 ℝ) (h : env = nestedFields old) : NestedInput where
  M := env.read 0
  a := env.read 1
  d := env.read 2
  c := env.read 3
  t := env.read 4
  q := env.read 5
  a_pos := by simpa [h,nestedFields,FixedArrayTable.read_ofFn] using old.a_pos
  d_pos := by simpa [h,nestedFields,FixedArrayTable.read_ofFn] using old.d_pos
  c_pos := by simpa [h,nestedFields,FixedArrayTable.read_ofFn] using old.c_pos
  t_pos := by simpa [h,nestedFields,FixedArrayTable.read_ofFn] using old.t_pos
  t_lt := by simpa [h,nestedFields,FixedArrayTable.read_ofFn] using old.t_lt
  q_pos := by simpa [h,nestedFields,FixedArrayTable.read_ofFn] using old.q_pos
  q_lt := by simpa [h,nestedFields,FixedArrayTable.read_ofFn] using old.q_lt
  a_le := by simpa [h,nestedFields,FixedArrayTable.read_ofFn] using old.a_le
  d_le := by simpa [h,nestedFields,FixedArrayTable.read_ofFn] using old.d_le
  c_le := by simpa [h,nestedFields,FixedArrayTable.read_ofFn] using old.c_le
  ordered := by simpa [h,nestedFields,FixedArrayTable.read_ofFn] using old.ordered
  balance := by simpa [h,nestedFields,FixedArrayTable.read_ofFn] using old.balance

theorem storedNested_value (old : NestedInput) (env : FixedArrayTable 6 ℝ) (h : env = nestedFields old) :
    storedNested old env h = old := by
  cases h
  rfl

noncomputable def interiorInput (i : NestedSpec) (hq0 : 0 < i.q) (hq1 : i.q < 1) : Run NestedInput :=
  let a := arithmetic .minimum i.a i.d
  let d := arithmetic .maximum i.a i.d
  let fields := copyRow ![i.M,a.value,d.value,i.c,i.t,i.q]
  have hFields : fields.value = nestedFields (i.interiorInput hq0 hq1) := by
    apply table_ext
    intro j
    simp [fields,a,d,copyRow,arrayRun_read,arithmetic,Operation.realValue,RealArithmeticOp.apply,
      nestedFields,NestedSpec.interiorInput,FixedArrayTable.read_ofFn]
  join a (join d (join fields ⟨storedNested (i.interiorInput hq0 hq1) fields.value hFields,[]⟩))

theorem interiorInput_value (i : NestedSpec) (hq0 : 0 < i.q) (hq1 : i.q < 1) :
    (interiorInput i hq0 hq1).value = i.interiorInput hq0 hq1 := by
  simp only [interiorInput,join_value,storedNested_value]

theorem interiorInput_cost (i : NestedSpec) (hq0 : 0 < i.q) (hq1 : i.q < 1) : (interiorInput i hq0 hq1).cost ≤ 30 := by
  unfold interiorInput
  rw [join_cost,join_cost,join_cost,copyRow_cost]
  change 2 + (2 + (20 + 0)) ≤ 30
  decide

noncomputable def nestedSpecDraw (i : NestedSpec) (seed : Fin 11 → ℝ) : Run (FixedArrayTable 3 ℝ) :=
  let zero := compareLe i.q 0
  let one := compareLe 1 i.q
  let result := if hq0 : i.q = 0 then threeDraw (i.longInput hq0) (RealUniformInputs.dropInputs 9 2 seed) else
    if hq1 : i.q = 1 then threeDraw (i.shortInput hq1) (RealUniformInputs.dropInputs 9 2 seed) else
      let prepared := interiorInput i (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)
      let drawn := nestedDraw prepared.value seed
      let compared := compareLe i.a i.d
      let restored := if compared.value then drawn else join drawn (swapRow drawn.value)
      join prepared (join compared (join (⟨(),[.control]⟩ : Run Unit) restored))
  join zero (join one (join (⟨(),[.control,.control]⟩ : Run Unit) result))

theorem nestedSpecDraw_value (i : NestedSpec) (seed : Fin 11 → ℝ) :
    (nestedSpecDraw i seed).value.read = i.realSample seed := by
  unfold nestedSpecDraw NestedSpec.realSample
  simp only [join_value]
  by_cases hq0 : i.q = 0
  · simp only [dite_eq_left hq0]
    exact threeDraw_value _ _
  · simp only [dite_eq_right hq0]
    by_cases hq1 : i.q = 1
    · simp only [dite_eq_left hq1]
      exact threeDraw_value _ _
    · simp only [dite_eq_right hq1]
      by_cases had : i.a ≤ i.d
      · simp [join_value,interiorInput_value,compareLe,had,nestedDraw_value]
      · simp [join_value,interiorInput_value,compareLe,had,swapRow_value,nestedDraw_value]

theorem nestedSpecDraw_cost (i : NestedSpec) (seed : Fin 11 → ℝ) : (nestedSpecDraw i seed).cost ≤ 9500 := by
  unfold nestedSpecDraw
  rw [join_cost,join_cost,join_cost]
  have hz : (compareLe i.q 0).cost = 1 := rfl
  have ho : (compareLe 1 i.q).cost = 1 := rfl
  have hb : (⟨(),[Operation.control,.control]⟩ : Run Unit).cost = 2 := rfl
  rw [hz,ho,hb]
  split
  · rename_i hq0
    have hd := threeDraw_cost (i.longInput hq0) (RealUniformInputs.dropInputs 9 2 seed)
    omega
  · rename_i hq0
    split
    · rename_i hq1
      have hd := threeDraw_cost (i.shortInput hq1) (RealUniformInputs.dropInputs 9 2 seed)
      omega
    · rename_i hq1
      rw [join_cost,join_cost,join_cost]
      have hPos := lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)
      have hLt := lt_of_le_of_ne i.q_le hq1
      have hp := interiorInput_cost i hPos hLt
      have hd := nestedDraw_cost (interiorInput i hPos hLt).value seed
      have hs := swapRow_cost (nestedDraw (interiorInput i hPos hLt).value seed).value
      have hc : (compareLe i.a i.d).cost = 1 := rfl
      have ht : (⟨(),[Operation.control]⟩ : Run Unit).cost = 1 := rfl
      rw [hc,ht]
      split
      · omega
      · rw [join_cost]
        omega

theorem nestedSpecDraw_law (i : NestedSpec) :
    Measure.map (fun seed => (nestedSpecDraw i seed).value.read)
      (RealUniformInputs.law 11 : Measure (Fin 11 → ℝ)) = (i.law : Measure (Allocation 3)) := by
  have h : (fun seed => (nestedSpecDraw i seed).value.read) = i.realSample := funext (nestedSpecDraw_value i)
  rw [h]
  exact i.realSample_law

theorem nestedSpecDraw_fullBudget (i : NestedSpec) (seed : Fin 11 → ℝ)
    (h : ∀ j, 0 ≤ seed j ∧ seed j ≤ 1) : FullBudget i.M (nestedSpecDraw i seed).value.read := by
  rw [nestedSpecDraw_value]
  exact i.realSample_fullBudget seed h

end Blotto.RealPRGNativeFactoryExecution
