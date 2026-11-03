import Blotto.RealPRGNativeFactoryExecution
import Blotto.RealOverlapDescriptorCompiler

/-! Native table production for the four-variable gluing branch. Parent
factories, retained overlap environments and every output cell are evaluated
through named real-RAM operations; the original table and whole law are kept. -/
namespace Blotto.RealPRGFourNativeExecution
open MeasureTheory PRGRealRAMExecution PRGExactRealRAMContract RealPRGNativeFactoryExecution
open scoped BigOperators Classical

noncomputable def swappedFactory (prepared : PreparedSegment 3 9) : Run (PreparedSegment 3 9) :=
  assemble
    (arrayRun 9 (loadReal prepared.weight))
    (arrayRun 9 (fun slot => join (⟨(),[.control]⟩ : Run Unit) (swapRow (prepared.P.read slot))))
    (arrayRun 9 (fun slot => join (⟨(),[.control]⟩ : Run Unit) (swapRow (prepared.Q.read slot))))

theorem swappedFactory_value (l : SegmentLottery 3 9) :
    (swappedFactory (PreparedSegment.ofLottery l)).value =
      PreparedSegment.ofLottery (l.mapped AffineAllocation.swapFirst) := by
  apply prepared_ext
  · apply table_ext
    intro slot
    simp [swappedFactory,assemble,arrayRun_read,loadReal,Operation.realValue,
      PreparedSegment.ofLottery,FixedArrayTable.read_ofFn,SegmentLottery.mapped]
  · apply table_ext
    intro slot
    apply table_ext
    intro j
    have hs := congrFun (swapRow_value ((PreparedSegment.ofLottery l).P.read slot)) j
    simpa only [swappedFactory,assemble,arrayRun_read,join_value,PreparedSegment.ofLottery,
      FixedArrayTable.read_ofFn,SegmentLottery.mapped,AffineAllocation.swapFirst,swapFirst] using hs
  · apply table_ext
    intro slot
    apply table_ext
    intro j
    have hs := congrFun (swapRow_value ((PreparedSegment.ofLottery l).Q.read slot)) j
    simpa only [swappedFactory,assemble,arrayRun_read,join_value,PreparedSegment.ofLottery,
      FixedArrayTable.read_ofFn,SegmentLottery.mapped,AffineAllocation.swapFirst,swapFirst] using hs

theorem swappedFactory_cost (prepared : PreparedSegment 3 9) : (swappedFactory prepared).cost ≤ 300 := by
  have hw := arrayRun_bound 9 1 (loadReal prepared.weight) (fun _ => by rfl)
  have hP := arrayRun_bound 9 12 (fun slot => join (⟨(),[Operation.control]⟩ : Run Unit) (swapRow (prepared.P.read slot)))
    (fun slot => by rw [join_cost]; have h := swapRow_cost (prepared.P.read slot); change 1 + _ ≤ _; omega)
  have hQ := arrayRun_bound 9 12 (fun slot => join (⟨(),[Operation.control]⟩ : Run Unit) (swapRow (prepared.Q.read slot)))
    (fun slot => by rw [join_cost]; have h := swapRow_cost (prepared.Q.read slot); change 1 + _ ≤ _; omega)
  unfold swappedFactory
  rw [assemble_cost]
  omega

noncomputable def threeFactory (i : ThreeSpec) : Run (PreparedSegment 3 9) :=
  let input := orderedThreeInput i
  let prepared := orderedFactory input.value
  let compared := compareLe i.a i.d
  let restored := if compared.value then prepared else join prepared (swappedFactory prepared.value)
  join input (join compared (join (⟨(),[.control]⟩ : Run Unit) restored))

theorem threeFactory_value (i : ThreeSpec) :
    (threeFactory i).value = PreparedSegment.ofLottery i.segmentLottery := by
  simp only [threeFactory,join_value,orderedThreeInput_value,compareLe,decide_eq_true_eq]
  unfold ThreeSpec.segmentLottery
  by_cases h : i.a ≤ i.d
  · simp only [h,ite_true,orderedFactory_value]
  · simp only [h,ite_false,join_value,orderedFactory_value,swappedFactory_value]

theorem threeFactory_cost (i : ThreeSpec) : (threeFactory i).cost ≤ 6700 := by
  have hi := orderedThreeInput_cost i
  have hp := orderedFactory_cost (orderedThreeInput i).value
  have hs := swappedFactory_cost (orderedFactory (orderedThreeInput i).value).value
  unfold threeFactory
  rw [join_cost,join_cost,join_cost]
  have hc : (compareLe i.a i.d).cost = 1 := rfl
  have hb : (⟨(),[Operation.control]⟩ : Run Unit).cost = 1 := rfl
  rw [hc,hb]
  split
  · omega
  · rw [join_cost]
    omega

noncomputable def overlapEnvironment {k h : ℕ} (first : PreparedSegment 3 k) (second : PreparedSegment 3 h)
    (d B : ℝ) (i : Fin k) (j : Fin h) : Run (FixedArrayTable 16 ℝ) :=
  join (⟨(),[.control,.control,.control,.control,.control]⟩ : Run Unit)
    (copyRow ![(first.P.read i).read 0,(first.P.read i).read 1,(first.P.read i).read 2,
      (first.Q.read i).read 0,(first.Q.read i).read 1,(first.Q.read i).read 2,
      (second.P.read j).read 0,(second.P.read j).read 1,(second.P.read j).read 2,
      (second.Q.read j).read 0,(second.Q.read j).read 1,(second.Q.read j).read 2,
      first.weight.read i,second.weight.read j,d,B])

theorem overlapEnvironment_value {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h) :
    (overlapEnvironment (PreparedSegment.ofLottery G.first) (PreparedSegment.ofLottery G.second) G.d B i j).value =
      RealOverlapFormula.environment G B i j := by
  apply table_ext
  intro r
  simp [overlapEnvironment,join_value,copyRow_read,PreparedSegment.ofLottery,
    FixedArrayTable.read_ofFn,RealOverlapFormula.environment]

theorem overlapEnvironment_cost {k h : ℕ} (first : PreparedSegment 3 k) (second : PreparedSegment 3 h)
    (d B : ℝ) (i : Fin k) (j : Fin h) : (overlapEnvironment first second d B i j).cost ≤ 60 := by
  unfold overlapEnvironment
  rw [join_cost,copyRow_cost]
  change 5 + (3 * 16 + 2) ≤ 60
  decide

noncomputable def storedExpression {N : ℕ} (envs : FixedArrayTable N (FixedArrayTable 16 ℝ))
    (slot : Fin N) (e : RationalExpression 16) : Run ℝ :=
  join (⟨(),[.control]⟩ : Run Unit) (expression (envs.read slot) e)

@[simp] theorem storedExpression_value {N : ℕ} (envs : FixedArrayTable N (FixedArrayTable 16 ℝ))
    (slot : Fin N) (e : RationalExpression 16) : (storedExpression envs slot e).value = e.realValue (envs.read slot) := by
  simp [storedExpression,join_value,expression_value]

theorem storedExpression_cost {N : ℕ} (envs : FixedArrayTable N (FixedArrayTable 16 ℝ))
    (slot : Fin N) (e : RationalExpression 16) : (storedExpression envs slot e).cost ≤ 2 * e.operationBound + 1 := by
  have h := expression_cost (envs.read slot) e
  unfold storedExpression
  rw [join_cost]
  change 1 + _ ≤ _
  omega

noncomputable def overlapEnvironments {k h : ℕ} (first : PreparedSegment 3 k) (second : PreparedSegment 3 h)
    (d B : ℝ) : Run (FixedArrayTable (k * h) (FixedArrayTable 16 ℝ)) :=
  arrayRun (k * h) (fun slot =>
    overlapEnvironment first second d B (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)

theorem overlapEnvironments_value {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) :
    (overlapEnvironments (PreparedSegment.ofLottery G.first) (PreparedSegment.ofLottery G.second) G.d B).value =
      FixedArrayTable.ofFn (fun slot => RealOverlapFormula.environment G B
        (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2) := by
  apply table_ext
  intro slot
  rw [FixedArrayTable.read_ofFn]
  exact (arrayRun_read (k * h) _ slot).trans (overlapEnvironment_value G B _ _)

theorem overlapEnvironments_cost {k h : ℕ} (first : PreparedSegment 3 k) (second : PreparedSegment 3 h)
    (d B : ℝ) : (overlapEnvironments first second d B).cost ≤ 62 * (k * h) + 2 := by
  exact (arrayRun_bound (k * h) 60 _ (fun slot => overlapEnvironment_cost _ _ _ _ _ _)).trans_eq (by omega)

noncomputable def overlapDescriptor {N : ℕ} (envs : FixedArrayTable N (FixedArrayTable 16 ℝ)) : Run (PreparedSegment 4 N) :=
  assemble
    (arrayRun N (fun slot => storedExpression envs slot OverlapFormulaCode.weight))
    (arrayRun N (fun slot => arrayRun 4 (fun r => storedExpression envs slot (OverlapFormulaCode.safeP r))))
    (arrayRun N (fun slot => arrayRun 4 (fun r => storedExpression envs slot (OverlapFormulaCode.safeQ r))))

theorem overlapDescriptor_value {k h : ℕ} (G : OverlapGluing k h) (B : ℝ)
    (hFirst : G.firstProbe = AffineProbe.coordinate 2)
    (hSecond : G.secondProbe = AffineProbe.reflectedCoordinate G.d 0) :
    (overlapDescriptor (FixedArrayTable.ofFn (fun slot => RealOverlapFormula.environment G B
        (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2))).value =
      PreparedSegment.ofLottery (G.descriptor B) := by
  apply prepared_ext
  · apply table_ext
    intro slot
    simp only [overlapDescriptor,assemble,arrayRun_read,storedExpression_value,
      PreparedSegment.ofLottery,FixedArrayTable.read_ofFn,OverlapGluing.descriptor]
    exact RealOverlapFormula.weight_value G B _ _ hFirst hSecond
  · apply table_ext
    intro slot
    apply table_ext
    intro r
    simp only [overlapDescriptor,assemble,arrayRun_read,storedExpression_value,
      PreparedSegment.ofLottery,FixedArrayTable.read_ofFn,OverlapGluing.descriptor]
    exact RealOverlapFormula.safeP_value G B _ _ hFirst hSecond r
  · apply table_ext
    intro slot
    apply table_ext
    intro r
    simp only [overlapDescriptor,assemble,arrayRun_read,storedExpression_value,
      PreparedSegment.ofLottery,FixedArrayTable.read_ofFn,OverlapGluing.descriptor]
    exact RealOverlapFormula.safeQ_value G B _ _ hFirst hSecond r

theorem overlapDescriptor_cost {N : ℕ} (envs : FixedArrayTable N (FixedArrayTable 16 ℝ)) :
    (overlapDescriptor envs).cost ≤ 4500 * N + 10 := by
  have hw := arrayRun_bound N 257 (fun slot => storedExpression envs slot OverlapFormulaCode.weight)
    (fun slot => (storedExpression_cost envs slot _).trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 2 OverlapFormulaCode.weight_operationBound) 1))
  have hPcell : ∀ slot, (arrayRun 4 (fun r => storedExpression envs slot (OverlapFormulaCode.safeP r))).cost ≤ 2062 :=
    fun slot => arrayRun_bound 4 513 _ (fun r => (storedExpression_cost envs slot _).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (OverlapFormulaCode.safeP_operationBound r)) 1))
  have hQcell : ∀ slot, (arrayRun 4 (fun r => storedExpression envs slot (OverlapFormulaCode.safeQ r))).cost ≤ 2062 :=
    fun slot => arrayRun_bound 4 513 _ (fun r => (storedExpression_cost envs slot _).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (OverlapFormulaCode.safeQ_operationBound r)) 1))
  have hP := arrayRun_bound N 2062 _ hPcell
  have hQ := arrayRun_bound N 2062 _ hQcell
  unfold overlapDescriptor
  rw [assemble_cost]
  omega

noncomputable def overlapFactory {k h : ℕ} (first : PreparedSegment 3 k) (second : PreparedSegment 3 h)
    (d B : ℝ) : Run (PreparedSegment 4 (k * h)) :=
  let envs := overlapEnvironments first second d B
  join envs (overlapDescriptor envs.value)

theorem overlapFactory_value {k h : ℕ} (G : OverlapGluing k h) (B : ℝ)
    (hFirst : G.firstProbe = AffineProbe.coordinate 2)
    (hSecond : G.secondProbe = AffineProbe.reflectedCoordinate G.d 0) :
    (overlapFactory (PreparedSegment.ofLottery G.first) (PreparedSegment.ofLottery G.second) G.d B).value =
      PreparedSegment.ofLottery (G.descriptor B) := by
  simp only [overlapFactory,join_value,overlapEnvironments_value]
  exact overlapDescriptor_value G B hFirst hSecond

theorem overlapFactory_cost {k h : ℕ} (first : PreparedSegment 3 k) (second : PreparedSegment 3 h)
    (d B : ℝ) : (overlapFactory first second d B).cost ≤ 5000 * (k * h) + 20 := by
  have he := overlapEnvironments_cost first second d B
  have hd := overlapDescriptor_cost (overlapEnvironments first second d B).value
  unfold overlapFactory
  rw [join_cost]
  omega

noncomputable def fourParameters (i : FourInput) : Run (RealFourParameterTable i) :=
  let env := copyRow ![i.B,i.u,i.v,i.w,i.ell,i.p]
  let fields := arrayRun 8 (fun j => expression env.value (RationalFourParametersCode.programs j))
  have hEnv : env.value = RealFourParametersCode.environment i := by
    apply table_ext
    intro j
    simp [env,copyRow,arrayRun_read,RealFourParametersCode.environment,FixedArrayTable.read_ofFn]
  let prepared : RealFourParameterTable i := ⟨fields.value,fun j => by
    rw [arrayRun_read,expression_value,hEnv]
    exact RealFourParametersCode.value_eq i j⟩
  join env (join fields ⟨prepared,[]⟩)

theorem fourParameters_cost (i : FourInput) : (fourParameters i).cost ≤ 4200 := by
  have he := copyRow_cost ![i.B,i.u,i.v,i.w,i.ell,i.p]
  have hp := arrayRun_bound 8 512 (fun j => expression (copyRow ![i.B,i.u,i.v,i.w,i.ell,i.p]).value (RationalFourParametersCode.programs j))
    (fun j => (expression_cost _ _).trans (Nat.mul_le_mul_left 2 (RationalFourParametersCode.operationBound j)))
  unfold fourParameters
  rw [join_cost,join_cost]
  change _ + (_ + 0) ≤ _
  omega

noncomputable def gluingFactory (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) : Run (PreparedSegment 4 81) :=
  let params := fourParameters i
  let first := threeFactory (params.value.gluingFirstSpec hcase)
  let second := threeFactory (params.value.gluingSecondSpec hcase)
  let result := overlapFactory first.value second.value params.value.auxLength i.B
  join params (join first (join second result))

theorem gluingFactory_value (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    (gluingFactory i hcase).value = PreparedSegment.ofLottery (i.gluingDescriptor hcase) := by
  simp only [gluingFactory,join_value,threeFactory_value,
    RealFourParameterTable.gluingFirstSpec_eq,RealFourParameterTable.gluingSecondSpec_eq,RealFourParameterTable.auxLength_eq]
  have h := overlapFactory_value (i.overlapData hcase) i.B rfl rfl
  exact h

theorem gluingFactory_cost (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    (gluingFactory i hcase).cost ≤ 423000 := by
  have hp := fourParameters_cost i
  have hFirst := threeFactory_cost ((fourParameters i).value.gluingFirstSpec hcase)
  have hSecond := threeFactory_cost ((fourParameters i).value.gluingSecondSpec hcase)
  have hOverlap := overlapFactory_cost
    (threeFactory ((fourParameters i).value.gluingFirstSpec hcase)).value
    (threeFactory ((fourParameters i).value.gluingSecondSpec hcase)).value
    (fourParameters i).value.auxLength i.B
  unfold gluingFactory
  rw [join_cost,join_cost,join_cost]
  omega

noncomputable def gluingDraw (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) (seed : Fin 81 → ℝ) : Run (FixedArrayTable 4 ℝ) :=
  let prepared := gluingFactory i hcase
  join prepared (draw prepared.value 0 seed)

theorem gluingDraw_value (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) (seed : Fin 81 → ℝ) :
    (gluingDraw i hcase seed).value.read = i.realGluingSample hcase seed := by
  simp only [gluingDraw,join_value,gluingFactory_value,draw_value]
  rw [i.realGluingSample_refines hcase]

theorem gluingDraw_cost (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) (seed : Fin 81 → ℝ) :
    (gluingDraw i hcase seed).cost ≤ 425000 := by
  have hp := gluingFactory_cost i hcase
  have hd := draw_cost (gluingFactory i hcase).value 0 seed
  unfold gluingDraw
  rw [join_cost]
  omega

theorem gluingDraw_law (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    Measure.map (fun seed => (gluingDraw i hcase seed).value.read)
      (RealUniformInputs.law 81 : Measure (Fin 81 → ℝ)) = (i.gluingCaseLaw hcase : Measure (Allocation 4)) := by
  have h : (fun seed => (gluingDraw i hcase seed).value.read) = i.realGluingSample hcase := funext (gluingDraw_value i hcase)
  rw [h]
  exact i.realGluingSample_law hcase

theorem gluingDraw_fullBudget (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) (seed : Fin 81 → ℝ)
    (h : 0 ≤ seed 0 ∧ seed 0 ≤ 1) : FullBudget i.B (gluingDraw i hcase seed).value.read := by
  rw [gluingDraw_value]
  exact i.realGluingSample_fullBudget hcase seed h

end Blotto.RealPRGFourNativeExecution
