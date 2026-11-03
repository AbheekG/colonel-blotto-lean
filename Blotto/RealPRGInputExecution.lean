import Blotto.RealPRGOriginalSampler
import Blotto.RealPRGNativeFactoryExecution

/-! Original ordered-budget preparation in the named exact-real RAM model.
Runtime inputs are an actual stored original-value array and available real
budget scalars. Mathematical input/system objects supply erased legality and
readback certificates only. Every numerical ratio/derived array is produced
by named loads/arithmetic/stores; no normalizedInput callback is executed to
produce a runtime operand. Array loops use the incoming stored header count.
The prepared records retain these arrays and original scaling data once. -/
namespace Blotto.RealPRGInputExecution
open PRGRealRAMExecution PRGExactRealRAMContract RealPRGNativeFactoryExecution
open scoped BigOperators Classical

noncomputable def scalar (address : ℕ) (value : ℝ) : Run ℝ := ⟨value,[.load address value]⟩

theorem scalar_cost (address : ℕ) (value : ℝ) : (scalar address value).cost = 1 := rfl

noncomputable def multiplyArray {n : ℕ} (coefficient : ℝ) (input : FixedArrayTable n ℝ) : Run (FixedArrayTable n ℝ) :=
  let count := input.data.size
  let computed := arrayRun count (fun j =>
    let loaded := loadReal input (j.cast input.size)
    join loaded (arithmetic .mul coefficient loaded.value))
  ⟨⟨computed.value.data,computed.value.size.trans input.size⟩,
    [.control] ++ computed.trace ++ [.storeCell 0]⟩

theorem multiplyArray_read {n : ℕ} (coefficient : ℝ) (input : FixedArrayTable n ℝ) (j : Fin n) :
    (multiplyArray coefficient input).value.read j = coefficient * input.read j := by
  unfold multiplyArray
  change (arrayRun input.data.size (fun k => join (loadReal input (k.cast input.size))
    (arithmetic .mul coefficient (loadReal input (k.cast input.size)).value))).value.read (j.cast input.size.symm) = _
  rw [arrayRun_read]
  change coefficient * input.read ((j.cast input.size.symm).cast input.size) = coefficient * input.read j
  apply congrArg (fun k => coefficient * input.read k)
  apply Fin.ext
  rfl

theorem multiplyArray_value {n : ℕ} (coefficient : ℝ) (input : FixedArrayTable n ℝ) :
    (multiplyArray coefficient input).value.read = fun j => coefficient * input.read j :=
  funext (multiplyArray_read coefficient input)

theorem multiplyArray_cost {n : ℕ} (coefficient : ℝ) (input : FixedArrayTable n ℝ) :
    (multiplyArray coefficient input).cost ≤ 4 * n + 4 := by
  have h := arrayRun_bound input.data.size 2
    (fun j => join (loadReal input (j.cast input.size))
      (arithmetic .mul coefficient (loadReal input (j.cast input.size)).value))
    (fun _ => by rw [join_cost]; change 1 + 1 ≤ 2; decide)
  unfold multiplyArray
  change cost ([.control] ++ _ ++ [.storeCell 0]) ≤ _
  rw [cost_append,cost_append]
  change 1 + (arrayRun input.data.size _).cost + 1 ≤ _
  dsimp only at *
  have hN : 2 + input.data.size * (2 + 2) = 4 * n + 2 := by rw [input.size]; omega
  have hFixed := h.trans_eq hN
  omega

private theorem values_ext {n : ℕ} (s t : Values n) (h : s.weight = t.weight) : s = t := by
  cases s
  cases t
  cases h
  rfl

private theorem input_ext {n : ℕ} (s t : PRGInput n) (hV : s.values = t.values) (hB : s.b = t.b) : s = t := by
  cases s
  cases t
  cases hV
  cases hB
  rfl

private theorem system_ext {n : ℕ} (s t : LottoResourceSystem n)
    (hB : s.B = t.B) (hL : s.length = t.length) (hI : s.initial = t.initial) : s = t := by
  cases s
  cases t
  cases hB
  cases hL
  cases hI
  rfl

/-- The old object is a legality certificate. Numerical fields all come from
the actual cached value table and computed ratio. Stores are charged by prepare. -/
private noncomputable def inputFromData {n : ℕ} (old : PRGInput n) (values : FixedArrayTable n ℝ)
    (hV : values.read = old.values.weight) (ratio : ℝ) (hRatio : ratio = old.b) : PRGInput n where
  values := ⟨values.read,by rw [hV]; exact old.values.positive,
    by rw [hV]; exact old.values.normalized⟩
  b := ratio
  b_pos := by rw [hRatio]; exact old.b_pos
  b_le := by rw [hRatio]; exact old.b_le
  small_fields := by
    change ∀ j, 2 * values.read j ≤ ratio
    rw [hV,hRatio]
    exact old.small_fields

private theorem inputFromData_value {n : ℕ} (old : PRGInput n) (values : FixedArrayTable n ℝ)
    (hV : values.read = old.values.weight) (ratio : ℝ) (hRatio : ratio = old.b) :
    inputFromData old values hV ratio hRatio = old := by
  apply input_ext
  · apply values_ext
    exact hV
  · exact hRatio

private noncomputable def systemFromData {n : ℕ} (old : LottoResourceSystem n)
    (budget : ℝ) (lengths initial : FixedArrayTable n ℝ)
    (hB : budget = old.B) (hL : lengths.read = old.length) (hI : initial.read = old.initial) : LottoResourceSystem n where
  B := budget
  length := lengths.read
  initial := initial.read
  B_pos := by rw [hB]; exact old.B_pos
  length_pos := by rw [hL]; exact old.length_pos
  length_le := by rw [hL,hB]; exact old.length_le
  initial_box := by rw [hL,hI]; exact old.initial_box
  initial_sum := by rw [hI,hB]; exact old.initial_sum

private theorem systemFromData_value {n : ℕ} (old : LottoResourceSystem n)
    (budget : ℝ) (lengths initial : FixedArrayTable n ℝ)
    (hB : budget = old.B) (hL : lengths.read = old.length) (hI : initial.read = old.initial) :
    systemFromData old budget lengths initial hB hL hI = old := system_ext _ _ hB hL hI

structure Prepared {n : ℕ} (i : RationalPRGOriginalInput n) where
  values : FixedArrayTable n ℝ
  scale : ℝ
  originalPoor : ℝ
  ratio : ℝ
  unitBudget : ℝ
  lengths : FixedArrayTable n ℝ
  poorInitial : FixedArrayTable n ℝ
  normalized : PRGInput n
  rich : LottoResourceSystem n
  poor : LottoResourceSystem n
  values_correct : values.read = i.realValues.weight
  scale_correct : scale = (i.a : ℝ)
  originalPoor_correct : originalPoor = (i.b : ℝ)
  ratio_correct : ratio = i.normalizedInput.real.b
  unitBudget_correct : unitBudget = 1
  lengths_correct : lengths.read = i.normalizedInput.real.richSystem.length
  poorInitial_correct : poorInitial.read = i.normalizedInput.real.poorSystem.initial
  normalized_correct : normalized = i.normalizedInput.real
  rich_correct : rich = i.normalizedInput.real.richSystem
  poor_correct : poor = i.normalizedInput.real.poorSystem
  rich_length : rich.length = lengths.read
  rich_initial : rich.initial = lengths.read
  poor_length : poor.length = lengths.read
  poor_initial : poor.initial = poorInitial.read
  rich_budget : rich.B = unitBudget
  poor_budget : poor.B = ratio

noncomputable def prepare {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ)) : Run (Prepared i) :=
  let richBudget := scalar 0 availableRich
  let poorBudget := scalar 1 availablePoor
  let ratio := arithmetic .div poorBudget.value richBudget.value
  let one := scalar 2 1
  let two := scalar 3 2
  let lengths := multiplyArray two.value values
  let poorInitial := multiplyArray ratio.value lengths.value
  have hRatio : ratio.value = i.normalizedInput.real.b := by
    change availablePoor / availableRich = ((i.b / i.a : ℚ) : ℝ)
    rw [hA,hB,Rat.cast_div]
  have hLength : lengths.value.read = i.normalizedInput.real.richSystem.length := by
    rw [multiplyArray_value]
    simp only [two,scalar,hV,PRGInput.richSystem]
    rfl
  have hInitial : poorInitial.value.read = i.normalizedInput.real.poorSystem.initial := by
    rw [multiplyArray_value,hRatio,hLength]
    rfl
  let normalized := inputFromData i.normalizedInput.real values hV ratio.value hRatio
  let rich := systemFromData i.normalizedInput.real.richSystem one.value lengths.value lengths.value rfl hLength hLength
  let poor := systemFromData i.normalizedInput.real.poorSystem ratio.value lengths.value poorInitial.value hRatio hLength hInitial
  let prepared : Prepared i :=
    ⟨values,richBudget.value,poorBudget.value,ratio.value,one.value,lengths.value,poorInitial.value,normalized,rich,poor,
      hV,hA,hB,hRatio,rfl,hLength,hInitial,inputFromData_value _ _ _ _ _,systemFromData_value _ _ _ _ _ _ _,
      systemFromData_value _ _ _ _ _ _ _,rfl,rfl,rfl,rfl,rfl,rfl⟩
  join richBudget <| join poorBudget <| join ratio <| join one <| join two <| join lengths <| join poorInitial <|
    ⟨prepared,
      -- Values wrapper and normalized input, then both three-field system records.
      [.storeCell 0,.control,.storeCell 1,.storeCell 2,.control,
       .storeCell 3,.storeCell 4,.storeCell 5,.control,
       .storeCell 6,.storeCell 7,.storeCell 8,.control,
       -- Complete retained preparation cache: four scalars and six native pointers.
       .store 9 richBudget.value,.store 10 poorBudget.value,.store 11 ratio.value,.store 12 one.value,
       .storeCell 13,.storeCell 14,.storeCell 15,.storeCell 16,.storeCell 17,.storeCell 18,.control]⟩

set_option maxHeartbeats 600000 in
theorem prepare_cost {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ)) :
    (prepare i values hV availableRich availablePoor hA hB).cost ≤ 8 * n + 50 := by
  have hLength := multiplyArray_cost (scalar 3 2).value values
  have hInitial := multiplyArray_cost
    (arithmetic .div (scalar 1 availablePoor).value (scalar 0 availableRich).value).value
    (multiplyArray (scalar 3 2).value values).value
  unfold prepare
  rw [join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost]
  simp only [scalar_cost]
  change 1 + (1 + (1 + (1 + (1 + (_ + (_ + 24)))))) ≤ 8 * n + 50
  omega

theorem prepare_values {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ)) :
    (prepare i values hV availableRich availablePoor hA hB).value.values = values := rfl

theorem prepare_scale {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ)) :
    (prepare i values hV availableRich availablePoor hA hB).value.scale = availableRich := rfl

theorem prepare_originalPoor {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ)) :
    (prepare i values hV availableRich availablePoor hA hB).value.originalPoor = availablePoor := rfl

theorem prepare_ratio {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ)) :
    (prepare i values hV availableRich availablePoor hA hB).value.ratio = availablePoor / availableRich := rfl

theorem prepare_length_read {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ)) (j : Fin n) :
    (prepare i values hV availableRich availablePoor hA hB).value.lengths.read j = 2 * values.read j := by
  change (multiplyArray 2 values).value.read j = _
  exact multiplyArray_read 2 values j

theorem prepare_poorInitial_read {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ)) (j : Fin n) :
    (prepare i values hV availableRich availablePoor hA hB).value.poorInitial.read j =
      (availablePoor / availableRich) * (2 * values.read j) := by
  change (multiplyArray (availablePoor / availableRich) (multiplyArray 2 values).value).value.read j = _
  rw [multiplyArray_read,multiplyArray_read]

theorem prepare_cost_from_header {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ)) :
    (prepare i values hV availableRich availablePoor hA hB).cost ≤ 8 * values.data.size + 50 := by
  rw [values.size]
  exact prepare_cost i values hV availableRich availablePoor hA hB

theorem Prepared.scale_ratio {n : ℕ} {i : RationalPRGOriginalInput n} (p : Prepared i) :
    p.scale * p.ratio = p.originalPoor := by
  rw [p.scale_correct,p.ratio_correct,p.originalPoor_correct]
  exact i.rescaled_poor_budget

theorem Prepared.normalized_budget {n : ℕ} {i : RationalPRGOriginalInput n} (p : Prepared i) :
    p.normalized.b = p.ratio := by
  rw [p.normalized_correct,p.ratio_correct]

theorem Prepared.normalized_values {n : ℕ} {i : RationalPRGOriginalInput n} (p : Prepared i) :
    p.normalized.values.weight = p.values.read := by
  rw [p.normalized_correct,p.values_correct]
  rfl

theorem prepare_normalized {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ)) :
    (prepare i values hV availableRich availablePoor hA hB).value.normalized = i.normalizedInput.real :=
  (prepare i values hV availableRich availablePoor hA hB).value.normalized_correct

theorem prepare_rich {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ)) :
    (prepare i values hV availableRich availablePoor hA hB).value.rich = i.normalizedInput.real.richSystem :=
  (prepare i values hV availableRich availablePoor hA hB).value.rich_correct

theorem prepare_poor {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (availableRich availablePoor : ℝ) (hA : availableRich = (i.a : ℝ)) (hB : availablePoor = (i.b : ℝ)) :
    (prepare i values hV availableRich availablePoor hA hB).value.poor = i.normalizedInput.real.poorSystem :=
  (prepare i values hV availableRich availablePoor hA hB).value.poor_correct

/-- A runtime-recognized ordered original PRG request, in real input cells. -/
def ValidData {n : ℕ} (values : FixedArrayTable n ℝ) (rich poor : ℝ) : Prop :=
  (∀ j, 0 < values.read j) ∧ (∑ j, values.read j) = 1 ∧
    0 < rich ∧ 0 < poor ∧ poor ≤ rich ∧ ∀ j, 2 * rich * values.read j ≤ poor

noncomputable def fieldCheck {n : ℕ} (values : FixedArrayTable n ℝ)
    (rich poor : ℝ) (j : Fin n) : Run (ℝ × Bool) :=
  let v := loadReal values j
  let two := scalar 2 2
  let twiceBudget := arithmetic .mul two.value rich
  let weighted := arithmetic .mul twiceBudget.value v.value
  let nonpositive := compareLe v.value 0
  let small := compareLe weighted.value poor
  ⟨(v.value,!nonpositive.value && small.value),
    v.trace ++ two.trace ++ twiceBudget.trace ++ weighted.trace ++ nonpositive.trace ++ small.trace ++
      [.control,.storeCell 0,.storeCell 1]⟩

theorem fieldCheck_value {n : ℕ} (values : FixedArrayTable n ℝ)
    (rich poor : ℝ) (j : Fin n) :
    (fieldCheck values rich poor j).value =
      (values.read j,decide (0 < values.read j ∧ 2 * rich * values.read j ≤ poor)) := by
  apply Prod.ext
  · rfl
  · change (!decide (values.read j ≤ 0) && decide (2 * rich * values.read j ≤ poor)) =
      decide (0 < values.read j ∧ 2 * rich * values.read j ≤ poor)
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,decide_eq_true_eq,not_le]

theorem fieldCheck_cost {n : ℕ} (values : FixedArrayTable n ℝ)
    (rich poor : ℝ) (j : Fin n) : (fieldCheck values rich poor j).cost = 9 := by
  simp [fieldCheck,loadReal,scalar,arithmetic,compareLe,Run.cost,Operation.cost]

noncomputable def foldChecks : List (ℝ × Bool) → Run (ℝ × Bool)
  | [] => ⟨(0,true),[.load 0 0,.control,.storeCell 0,.storeCell 1]⟩
  | item :: rest =>
      let later := foldChecks rest
      let sum := arithmetic .add item.1 later.value.1
      ⟨(sum.value,item.2 && later.value.2),
        later.trace ++ [.load 0 item.1,.control] ++ sum.trace ++
          [.control,.storeCell 0,.storeCell 1,.control]⟩

theorem foldChecks_value (items : List (ℝ × Bool)) :
    (foldChecks items).value = ((items.map Prod.fst).sum,items.all Prod.snd) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp [foldChecks,ih,arithmetic,Operation.realValue,RealArithmeticOp.apply]

theorem foldChecks_cost (items : List (ℝ × Bool)) :
    (foldChecks items).cost = 7 * items.length + 4 := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    change cost (_ ++ _ ++ _ ++ _) = _
    rw [cost_append,cost_append,cost_append]
    change (foldChecks rest).cost + 2 + 1 + 4 = _
    rw [ih,List.length_cons]
    omega

/-- Check positivity, normalization, budget order and every small-field
promise using actual stored cells and named arithmetic/comparison primitives. -/
noncomputable def recognize {n : ℕ} (values : FixedArrayTable n ℝ) (rich poor : ℝ) : Run Bool :=
  let richBudget := scalar 0 rich
  let poorBudget := scalar 1 poor
  let fields := arrayRun values.data.size (fun j =>
    fieldCheck values richBudget.value poorBudget.value (j.cast values.size))
  let folded := foldChecks fields.value.data.toList
  let richNonpositive := compareLe richBudget.value 0
  let poorNonpositive := compareLe poorBudget.value 0
  let ordered := compareLe poorBudget.value richBudget.value
  let sumUpper := compareLe folded.value.1 1
  let sumLower := compareLe 1 folded.value.1
  ⟨folded.value.2 && !richNonpositive.value && !poorNonpositive.value && ordered.value && sumUpper.value && sumLower.value,
    richBudget.trace ++ poorBudget.trace ++ fields.trace ++
      (List.replicate values.data.size [.control,.storeCell 0]).flatten ++ [.control] ++
      folded.trace ++ richNonpositive.trace ++ poorNonpositive.trace ++ ordered.trace ++
      sumUpper.trace ++ sumLower.trace ++ List.replicate 7 .control⟩

theorem recognize_value {n : ℕ} (values : FixedArrayTable n ℝ) (rich poor : ℝ) :
    (recognize values rich poor).value = decide (ValidData values rich poor) := by
  cases values with
  | mk data size =>
    cases size
    have ht : (arrayRun data.size (fun j => fieldCheck (⟨data,rfl⟩ : FixedArrayTable data.size ℝ)
        rich poor j)).value = FixedArrayTable.ofFn (fun j =>
          ((⟨data,rfl⟩ : FixedArrayTable data.size ℝ).read j,
            decide (0 < (⟨data,rfl⟩ : FixedArrayTable data.size ℝ).read j ∧
              2 * rich * (⟨data,rfl⟩ : FixedArrayTable data.size ℝ).read j ≤ poor))) := by
      apply table_ext
      intro j
      rw [arrayRun_read,fieldCheck_value,FixedArrayTable.read_ofFn]
    apply Bool.eq_iff_iff.mpr
    change ((foldChecks (arrayRun data.size
      (fun j => fieldCheck (⟨data,rfl⟩ : FixedArrayTable data.size ℝ) rich poor j)).value.data.toList).value.2 &&
      !decide (rich ≤ 0) && !decide (poor ≤ 0) && decide (poor ≤ rich) &&
      decide ((foldChecks (arrayRun data.size
        (fun j => fieldCheck (⟨data,rfl⟩ : FixedArrayTable data.size ℝ) rich poor j)).value.data.toList).value.1 ≤ 1) &&
      decide (1 ≤ (foldChecks (arrayRun data.size
        (fun j => fieldCheck (⟨data,rfl⟩ : FixedArrayTable data.size ℝ) rich poor j)).value.data.toList).value.1)) = true ↔ _
    rw [ht,foldChecks_value]
    simp only [FixedArrayTable.ofFn,Array.toList_ofFn,List.map_ofFn,List.sum_ofFn,
      Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,decide_eq_true_eq,not_le]
    have hAll : (List.ofFn (fun j =>
        ((⟨data,rfl⟩ : FixedArrayTable data.size ℝ).read j,
          decide (0 < (⟨data,rfl⟩ : FixedArrayTable data.size ℝ).read j ∧
            2 * rich * (⟨data,rfl⟩ : FixedArrayTable data.size ℝ).read j ≤ poor)))).all Prod.snd = true ↔
        ∀ j, 0 < (⟨data,rfl⟩ : FixedArrayTable data.size ℝ).read j ∧
          2 * rich * (⟨data,rfl⟩ : FixedArrayTable data.size ℝ).read j ≤ poor := by
      rw [List.all_eq_true]
      constructor
      · intro h j
        exact of_decide_eq_true (h _ (List.mem_ofFn.mpr ⟨j,rfl⟩))
      · intro h pair hp
        obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
        exact decide_eq_true (h j)
    rw [hAll]
    unfold ValidData
    constructor
    · rintro ⟨⟨⟨⟨⟨hFields,ha⟩,hb⟩,hOrder⟩,hUpper⟩,hLower⟩
      exact ⟨fun j => (hFields j).1,le_antisymm hUpper hLower,ha,hb,hOrder,fun j => (hFields j).2⟩
    · rintro ⟨hp,hs,ha,hb,hOrder,hSmall⟩
      exact ⟨⟨⟨⟨⟨fun j => ⟨hp j,hSmall j⟩,ha⟩,hb⟩,hOrder⟩,hs.le⟩,hs.ge⟩

theorem recognize_cost {n : ℕ} (values : FixedArrayTable n ℝ) (rich poor : ℝ) :
    (recognize values rich poor).cost ≤ 20 * values.data.size + 30 := by
  have hf := arrayRun_bound values.data.size 9
    (fun j => fieldCheck values (scalar 0 rich).value (scalar 1 poor).value (j.cast values.size))
    (fun j => (fieldCheck_cost _ _ _ _).le)
  have hs := foldChecks_cost (arrayRun values.data.size
    (fun j => fieldCheck values (scalar 0 rich).value (scalar 1 poor).value (j.cast values.size))).value.data.toList
  rw [Array.length_toList,(arrayRun values.data.size _).value.size] at hs
  unfold recognize
  change cost (_ ++ _ ++ _ ++ _ ++ _ ++ _ ++ _ ++ _ ++ _ ++ _ ++ _ ++ _) ≤ _
  simp only [cost_append,cost_flatten,List.map_replicate,List.sum_replicate]
  change 1 + 1 + _ + values.data.size * 2 + 1 + _ + 1 + 1 + 1 + 1 + 1 + 7 ≤ _
  change cost (arrayRun values.data.size _).trace ≤ _ at hf
  change cost (foldChecks _).trace = _ at hs
  omega

theorem recognize_original {n : ℕ} (i : RationalPRGOriginalInput n)
    (values : FixedArrayTable n ℝ) (hV : values.read = i.realValues.weight)
    (rich poor : ℝ) (hA : rich = (i.a : ℝ)) (hB : poor = (i.b : ℝ)) :
    (recognize values rich poor).value = true := by
  rw [recognize_value,decide_eq_true_eq]
  unfold ValidData
  rw [hV,hA,hB]
  refine ⟨i.realValues.positive,i.realValues.normalized,?_,?_,?_,?_⟩
  · exact_mod_cast i.a_pos
  · exact_mod_cast i.b_pos
  · exact_mod_cast i.b_le
  · intro j
    change 2 * (i.a : ℝ) * (i.values j : ℝ) ≤ (i.b : ℝ)
    exact_mod_cast i.small_fields j

end Blotto.RealPRGInputExecution
