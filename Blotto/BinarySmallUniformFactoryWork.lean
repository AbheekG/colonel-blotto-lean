import Blotto.BinaryUnorderedThreeFactoryWork
import Blotto.BinarySmallUniformDrawWork
import Blotto.BinaryCachedFourParameterWork

/-! The original small-uniform producer retains parameters, three scale
products, its actual merged child, and every proportional endpoint split. All
primitive prices follow original fields and finite native geometry, including
total zero division. Copies/metadata/physical execution remain separate. -/

namespace Blotto.BinarySmallUniformFactoryWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryFactoryHeight
open BinarySmallUniformCompiler BinaryStoredOverlapEnvironment
open scoped BigOperators

def InputHeight (input : Input) (s : ℕ) : Prop := RationalHeight (value input.B) s ∧
  RationalHeight (value input.l0) s ∧ RationalHeight (value input.l1) s ∧
  RationalHeight (value input.l2) s ∧ RationalHeight (value input.l3) s

def splitWithWork (first second : SignedWord) (row : FixedArrayTable 3 SignedWord) : FixedArrayTable 4 SignedWord × ℕ :=
  let total := applyWithWork .add first second
  let low := applyWithWork .div first total.1
  let high := applyWithWork .div second total.1
  let left := applyWithWork .mul low.1 (row.read 0)
  let right := applyWithWork .mul high.1 (row.read 0)
  (FixedArrayTable.ofFn ![left.1,right.1,row.read 1,row.read 2],total.2 + low.2 + high.2 + left.2 + right.2)

theorem splitWithWork_state (first second : SignedWord) (row : FixedArrayTable 3 SignedWord) :
    (splitWithWork first second row).1 = BinarySmallUniformCompiler.split first second row := by
  unfold splitWithWork BinarySmallUniformCompiler.split
  simp only [applyWithWork_state]

theorem splitWithWork_bound (first second : SignedWord) (row : FixedArrayTable 3 SignedWord)
    (hC : CanonicalWord first) (hD : CanonicalWord second) (hRow : ∀ j, CanonicalWord (row.read j))
    (s : ℕ) (hf : RationalHeight (value first) s) (hs : RationalHeight (value second) s)
    (hr : ∀ j, RationalHeight (value (row.read j)) s) :
    (splitWithWork first second row).2 ≤ 5 * opcodeBound (expressionHeightBudget s 2) := by
  have hm1 := expressionHeightBudget_ge_input s 1
  have hm2 := expressionHeightBudget_ge_input s 2
  have hTotalC := BinaryReflectedFourSetup.opcode_canonical .add first second hC hD
  have hTotal : RationalHeight (value (apply .add first second)) (expressionHeightBudget s 1) := by
    rw [apply_value .add _ _ hC.1 hD.1]
    have h1 : RationalHeight (value first) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hf
    have h2 : RationalHeight (value second) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hs
    exact h1.add_level h2
  have hLowC := BinaryReflectedFourSetup.opcode_canonical .div first _ hC hTotalC
  have hHighC := BinaryReflectedFourSetup.opcode_canonical .div second _ hD hTotalC
  have hLow : RationalHeight (value (apply .div first (apply .add first second))) (expressionHeightBudget s 2) := by
    rw [apply_value .div _ _ hC.1 hTotalC.1]
    exact (hf.mono hm1).div_level hTotal
  have hHigh : RationalHeight (value (apply .div second (apply .add first second))) (expressionHeightBudget s 2) := by
    rw [apply_value .div _ _ hD.1 hTotalC.1]
    exact (hs.mono hm1).div_level hTotal
  have hT := opcode_bound .add first second hC hD _ (hf.mono hm2) (hs.mono hm2)
  have hTotal2 := hTotal.mono (expressionHeightBudget_mono s (by decide : 1 ≤ 2))
  have hL := opcode_bound .div first _ hC hTotalC _ (hf.mono hm2) hTotal2
  have hH := opcode_bound .div second _ hD hTotalC _ (hs.mono hm2) hTotal2
  have hP := opcode_bound .mul _ (row.read 0) hLowC (hRow 0) _ hLow ((hr 0).mono hm2)
  have hQ := opcode_bound .mul _ (row.read 0) hHighC (hRow 0) _ hHigh ((hr 0).mono hm2)
  unfold splitWithWork
  simp only [applyWithWork_state]
  omega

theorem child_height (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s) (h : InputHeight input s) :
    BinaryOrderedThreeFactoryWork.InputHeight (child input) (expressionHeightBudget s 1) := by
  have hm := expressionHeightBudget_ge_input s 1
  refine ⟨h.1.mono hm,?_,h.2.2.2.1.mono hm,h.2.2.2.2.mono hm,one_height _ (height_three hs)⟩
  change RationalHeight (value (apply .add input.l0 input.l1)) _
  rw [apply_value .add _ _ hC.2.1.1 hC.2.2.1.1]
  have hl : RationalHeight (value input.l0) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using h.2.1
  have hr : RationalHeight (value input.l1) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using h.2.2.1
  exact hl.add_level hr

def descriptorWithWork (input : Input) : Segment 4 9 × ℕ :=
  let total := applyWithWork .add input.l0 input.l1
  let child : BinaryThreeInputCompiler.Input := ⟨input.B,total.1,input.l2,input.l3,BinaryExpressionCompiler.Constant.one.word⟩
  let table := BinaryUnorderedThreeFactoryWork.descriptorWithWork child
  let first := FixedArrayTable.ofFn (fun slot => splitWithWork input.l0 input.l1 (table.1.P.read slot))
  let second := FixedArrayTable.ofFn (fun slot => splitWithWork input.l0 input.l1 (table.1.Q.read slot))
  (⟨table.1.weight,FixedArrayTable.ofFn (fun slot => (first.read slot).1),FixedArrayTable.ofFn (fun slot => (second.read slot).1)⟩,
    total.2 + table.2 + (∑ slot, (first.read slot).2) + (∑ slot, (second.read slot).2))

theorem descriptorWithWork_state (input : Input) : (descriptorWithWork input).1 = descriptor input := by
  unfold descriptorWithWork descriptor child
  simp only [applyWithWork_state,BinaryUnorderedThreeFactoryWork.descriptorWithWork_state,
    FixedArrayTable.read_ofFn,splitWithWork_state]

def descriptorBound (s : ℕ) : ℕ := opcodeBound s + BinaryUnorderedThreeFactoryWork.bound (expressionHeightBudget s 1) +
  90 * opcodeBound (expressionHeightBudget s 21)

theorem descriptorWithWork_bound (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s) (h : InputHeight input s) :
    (descriptorWithWork input).2 ≤ descriptorBound s := by
  have ht := opcode_bound .add input.l0 input.l1 hC.2.1 hC.2.2.1 s h.2.1 h.2.2.1
  have hChildC := child_canonical input hC
  have hChild := child_height input hC s hs h
  have hTableW := BinaryUnorderedThreeFactoryWork.descriptorWithWork_bound _ hChildC _ (height_three hs) hChild
  have hTable := BinaryUnorderedThreeFactoryWork.descriptor_height _ hChildC _ (height_three hs) hChild
  rw [expressionHeightBudget_comp] at hTable
  have hTC := BinaryThreeSpecCompiler.descriptor_canonical (child input) hChildC
  have hm := expressionHeightBudget_ge_input s 19
  have hp := fun slot => splitWithWork_bound input.l0 input.l1 _ hC.2.1 hC.2.2.1 (hTC.2.1 slot)
    _ (h.2.1.mono hm) (h.2.2.1.mono hm) (fun j => (hTable.2 slot j).1)
  have hq := fun slot => splitWithWork_bound input.l0 input.l1 _ hC.2.1 hC.2.2.1 (hTC.2.2 slot)
    _ (h.2.1.mono hm) (h.2.2.1.mono hm) (fun j => (hTable.2 slot j).2)
  have hP : (∑ slot : Fin 9, (splitWithWork input.l0 input.l1 ((BinaryThreeSpecCompiler.descriptor (child input)).P.read slot)).2) ≤
      45 * opcodeBound (expressionHeightBudget s 21) := by
    have he := Finset.sum_le_sum (fun slot (_ : slot ∈ (Finset.univ : Finset (Fin 9))) => hp slot)
    simpa only [expressionHeightBudget_comp,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,← Nat.mul_assoc] using he
  have hQ : (∑ slot : Fin 9, (splitWithWork input.l0 input.l1 ((BinaryThreeSpecCompiler.descriptor (child input)).Q.read slot)).2) ≤
      45 * opcodeBound (expressionHeightBudget s 21) := by
    have he := Finset.sum_le_sum (fun slot (_ : slot ∈ (Finset.univ : Finset (Fin 9))) => hq slot)
    simpa only [expressionHeightBudget_comp,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,← Nat.mul_assoc] using he
  unfold descriptorWithWork
  simp only [applyWithWork_state,BinaryUnorderedThreeFactoryWork.descriptorWithWork_state,FixedArrayTable.read_ofFn]
  change (applyWithWork .add input.l0 input.l1).2 + (BinaryUnorderedThreeFactoryWork.descriptorWithWork (child input)).2 + _ + _ ≤ _
  dsimp only [child] at hP hQ hTableW ⊢
  unfold descriptorBound
  omega

def prepareWithWork (input : BinaryFourParameters.Input) : Input × ℕ :=
  let parameters := BinaryFourParameters.prepareWithWork input
  let first := applyWithWork .mul (parameters.1.read 5) input.u
  let second := applyWithWork .mul (parameters.1.read 5) input.v
  let third := applyWithWork .mul (parameters.1.read 5) input.w
  (⟨input.B,first.1,second.1,third.1,input.ell⟩,parameters.2 + first.2 + second.2 + third.2)

theorem prepareWithWork_state (input : BinaryFourParameters.Input) : (prepareWithWork input).1 = prepare input := by
  unfold prepareWithWork prepare BinaryFourParameters.prepareWithWork
  simp only [applyWithWork_state]

def prepareBound (s : ℕ) : ℕ := BinaryCachedFourParameterWork.parameterBound s + 3 * opcodeBound (expressionHeightBudget s 12)

theorem prepareWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (s : ℕ) (hs : 2 ≤ s) (h : source.FieldsHeight s) :
    (prepareWithWork input).2 ≤ prepareBound s := by
  have hParam := BinaryFourParameters.prepareWork_bound input source hC hR s hs h.environment
  have hScale : RationalHeight (value ((BinaryFourParameters.prepare input).read 5)) (expressionHeightBudget s 12) := by
    rw [BinaryFourParameters.prepare_value input source hC hR 5]
    exact h.scalar hs 5
  have hm := expressionHeightBudget_ge_input s 12
  have hU : RationalHeight (value input.u) (expressionHeightBudget s 12) := by rw [hR.2.1]; exact h.2.1.mono hm
  have hV : RationalHeight (value input.v) (expressionHeightBudget s 12) := by rw [hR.2.2.1]; exact h.2.2.1.mono hm
  have hW : RationalHeight (value input.w) (expressionHeightBudget s 12) := by rw [hR.2.2.2.1]; exact h.2.2.2.1.mono hm
  have hu := opcode_bound .mul _ input.u (BinaryFourParameters.prepare_canonical input hC 5) hC.2.1 _ hScale hU
  have hv := opcode_bound .mul _ input.v (BinaryFourParameters.prepare_canonical input hC 5) hC.2.2.1 _ hScale hV
  have hw := opcode_bound .mul _ input.w (BinaryFourParameters.prepare_canonical input hC 5) hC.2.2.2.1 _ hScale hW
  unfold prepareWithWork BinaryFourParameters.prepareWithWork prepareBound BinaryCachedFourParameterWork.parameterBound
  dsimp only
  omega

theorem prepare_height (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell) (s : ℕ) (hs : 2 ≤ s) (h : source.FieldsHeight s) :
    InputHeight (prepare input) (expressionHeightBudget s 13) := by
  have hr := prepare_refines input source hC hR hCase
  have hh := h.smallUniformInput hs hCase
  unfold InputHeight
  rw [hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2]
  exact hh

def fromOriginalWithWork (input : BinaryFourParameters.Input) : Segment 4 9 × ℕ :=
  let prepared := prepareWithWork input
  let table := descriptorWithWork prepared.1
  (table.1,prepared.2 + table.2)

theorem fromOriginalWithWork_state (input : BinaryFourParameters.Input) : (fromOriginalWithWork input).1 = fromOriginal input := by
  unfold fromOriginalWithWork fromOriginal
  rw [descriptorWithWork_state,prepareWithWork_state]

def bound (s : ℕ) : ℕ := prepareBound s + descriptorBound (expressionHeightBudget s 13)

theorem fromOriginalWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell) (s : ℕ) (hs : 2 ≤ s) (h : source.FieldsHeight s) :
    (fromOriginalWithWork input).2 ≤ bound s := by
  have hP := prepareWithWork_bound input source hC hR s hs h
  have hs13 : 3 ≤ expressionHeightBudget s 13 := by unfold expressionHeightBudget; omega
  have hD := descriptorWithWork_bound _ (prepare_canonical input hC) _ hs13 (prepare_height input source hC hR hCase s hs h)
  unfold fromOriginalWithWork
  dsimp only
  rw [prepareWithWork_state]
  exact Nat.add_le_add hP hD

end Blotto.BinarySmallUniformFactoryWork
