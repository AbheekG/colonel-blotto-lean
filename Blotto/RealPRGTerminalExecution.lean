import Blotto.RealPRGPackingExecution
import Blotto.RealPRGReflectedExecution
import Blotto.RealTerminalSampler
import Blotto.RealPRGGroupExecution
import Blotto.PairStoreMemory

/-! Complete terminal preparation/drawing in the declared exact-real RAM.
Incoming capacity/resource arrays are actual stored buffers. Proof fields
identify them with the mathematical terminal input; they are not cost oracles.
Private mutable route cells have an explicit fixed-region store semantics.
Native Lean arrays denote those cells and do not assert host array-copy costs. -/

namespace Blotto.RealPRGTerminalExecution
open PRGRealRAMExecution PRGExactRealRAMContract RealPRGNativeFactoryExecution
open MeasureTheory
open scoped BigOperators Classical

noncomputable def strictCompare (x y : ℝ) : Run Bool :=
  ⟨decide (x < y), [.strictComparison x y]⟩

noncomputable def tests {n : ℕ} (lengths resources : FixedArrayTable n ℝ)
    (j : Fin n) : Run (Bool × Bool) :=
  let l := loadReal lengths j
  let r := loadReal resources j
  let first := compareLe r.value l.value
  let second := compareLe l.value r.value
  let positive := strictCompare 0 r.value
  let below := strictCompare r.value l.value
  ⟨(first.value && second.value, positive.value && below.value),
    l.trace ++ r.trace ++ first.trace ++ second.trace ++ positive.trace ++ below.trace ++
      [.control, .control, .storeCell 0, .storeCell 1]⟩

theorem tests_value {n : ℕ} (lengths resources : FixedArrayTable n ℝ) (j : Fin n) :
    (tests lengths resources j).value =
      (decide (resources.read j = lengths.read j),
        decide (0 < resources.read j ∧ resources.read j < lengths.read j)) := by
  apply Prod.ext
  · apply Bool.eq_iff_iff.mpr
    simp only [tests, loadReal, Operation.realValue, compareLe,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · intro h; exact le_antisymm (of_decide_eq_true h.1) (of_decide_eq_true h.2)
    · intro h; exact ⟨decide_eq_true (le_of_eq h), decide_eq_true (le_of_eq h.symm)⟩
  · simp only [tests, loadReal, Operation.realValue, compareLe, strictCompare, Bool.decide_and]
    rfl

theorem tests_cost {n : ℕ} (lengths resources : FixedArrayTable n ℝ) (j : Fin n) :
    (tests lengths resources j).cost = 10 := by
  simp [tests, loadReal, compareLe, strictCompare, Run.cost, Operation.cost]

noncomputable def classify {n : ℕ} (lengths resources : FixedArrayTable n ℝ) :
    List (Fin n) → Run (List (Fin n) × Option (Fin n))
  | [] => ⟨([], none), [.control]⟩
  | j :: rest =>
      let flags := tests lengths resources j
      let later := classify lengths resources rest
      let members := if flags.value.1 then j :: later.value.1 else later.value.1
      let pivot := if flags.value.2 then some j else later.value.2
      ⟨(members, pivot), flags.trace ++ later.trace ++
        (if flags.value.1 then [.storeCell j.val, .control] else []) ++
        [.control, .control, .storeCell 0, .storeCell 1]⟩

theorem classify_value {n : ℕ} (lengths resources : FixedArrayTable n ℝ) (items : List (Fin n)) :
    (classify lengths resources items).value =
      (items.filter (fun j => decide (resources.read j = lengths.read j)),
        items.find? (fun j => decide (0 < resources.read j ∧ resources.read j < lengths.read j))) := by
  induction items with
  | nil => rfl
  | cons j rest ih =>
      simp only [classify, tests_value, ih, List.filter_cons, List.find?_cons]
      cases h : decide (0 < resources.read j ∧ resources.read j < lengths.read j) <;> simp

theorem classify_cost {n : ℕ} (lengths resources : FixedArrayTable n ℝ) (items : List (Fin n)) :
    (classify lengths resources items).cost ≤ 16 * items.length + 1 := by
  induction items with
  | nil => exact le_rfl
  | cons j rest ih =>
      unfold classify
      change cost (_ ++ _ ++ _ ++ _) ≤ _
      simp only [cost_append]
      change (tests lengths resources j).cost + (classify lengths resources rest).cost +
        cost (if (tests lengths resources j).value.1 then [.storeCell j.val, .control] else []) + 4 ≤ _
      rw [tests_cost]
      split <;> simp only [cost_cons, cost_nil, Operation.cost, List.length_cons] <;> omega

noncomputable def indexList (n : ℕ) : Run (List (Fin n)) :=
  let array := arrayRun n (fun j => (⟨j, [.control]⟩ : Run (Fin n)))
  ⟨array.value.data.toList, array.trace ++
    (List.replicate n [.control, .storeCell 0]).flatten ++ [.control]⟩

theorem indexList_value (n : ℕ) : (indexList n).value = List.finRange n := by
  have h : (arrayRun n (fun j => (⟨j, [.control]⟩ : Run (Fin n)))).value =
      FixedArrayTable.ofFn (fun j => j) := by
    apply table_ext
    intro j
    rw [arrayRun_read, FixedArrayTable.read_ofFn]
  unfold indexList
  dsimp only
  rw [h]
  simp [FixedArrayTable.ofFn, List.finRange]

theorem indexList_cost (n : ℕ) : (indexList n).cost = 5 * n + 3 := by
  unfold indexList
  change cost (_ ++ _ ++ _) = _
  simp only [cost_append, cost_flatten, List.map_replicate, List.sum_replicate]
  change (arrayRun n _).cost + n * 2 + 1 = _
  rw [arrayRun_cost]
  simp [Run.cost, Operation.cost]
  omega

def listLength {α : Type*} : List α → Run ℕ
  | [] => ⟨0, [.control]⟩
  | _ :: rest =>
      let later := listLength rest
      ⟨later.value + 1, [.control, .control, .control] ++ later.trace⟩

theorem listLength_value {α : Type*} (items : List α) : (listLength items).value = items.length := by
  induction items with
  | nil => rfl
  | cons x rest ih => simp [listLength, ih]

theorem listLength_cost {α : Type*} (items : List α) : (listLength items).cost = 3 * items.length + 1 := by
  induction items with
  | nil => rfl
  | cons x rest ih =>
      change cost (_ ++ (listLength rest).trace) = _
      rw [cost_append]
      change 3 + (listLength rest).cost = _
      rw [ih, List.length_cons]
      omega

def listGet {α : Type*} : (items : List α) → Fin items.length → Run α
  | [], j => nomatch j
  | x :: rest, j =>
      if h : j.val = 0 then ⟨x, [.control, .control, .control]⟩
      else
        let later := listGet rest ⟨j.val - 1, by have hj := j.isLt; simp only [List.length_cons] at hj; omega⟩
        ⟨later.value, [.control, .control] ++ later.trace⟩

theorem listGet_value {α : Type*} (items : List α) (j : Fin items.length) :
    (listGet items j).value = items.get j := by
  induction items with
  | nil => exact Fin.elim0 j
  | cons x rest ih =>
      unfold listGet
      split
      · rename_i h
        simp [List.get_eq_getElem, h]
      · rename_i h
        rw [ih]
        cases j with
        | mk v hv =>
          cases v with
          | zero => exact False.elim (h rfl)
          | succ v => simp only [List.get_eq_getElem, Nat.succ_sub_one, List.getElem_cons_succ]

theorem listGet_cost {α : Type*} (items : List α) (j : Fin items.length) :
    (listGet items j).cost = 2 * j.val + 3 := by
  induction items with
  | nil => exact Fin.elim0 j
  | cons x rest ih =>
      unfold listGet
      split
      · rename_i h
        simp [Run.cost, Operation.cost, h]
      · rename_i h
        change cost (_ ++ _) = _
        rw [cost_append]
        change 2 + (listGet rest ⟨j.val - 1, _⟩).cost = _
        rw [ih]
        dsimp only
        omega

noncomputable def listArray {α : Type*} (items : List α) (count : ℕ) (h : count = items.length) :
    Run (FixedArrayTable count α) :=
  arrayRun count (fun j => listGet items (j.cast h))

theorem listArray_read {α : Type*} (items : List α) (count : ℕ) (h : count = items.length) (j : Fin count) :
    (listArray items count h).value.read j = items.get (j.cast h) := by
  simp only [listArray, arrayRun_read, listGet_value]

theorem listArray_cost {α : Type*} (items : List α) (count : ℕ) (h : count = items.length) :
    (listArray items count h).cost ≤ 2 + count * (2 * count + 3) := by
  unfold listArray
  apply arrayRun_bound count (2 * count + 1) _
  intro j
  rw [listGet_cost]
  have hj := j.isLt
  simp only [Fin.val_cast]
  omega

structure ClassifiedPacking {n : ℕ} (i : TerminalLotto n) where
  packing : RealTerminalPacking i
  pivot : Option (Fin n)
  pivot_correct : pivot = i.realPivot

noncomputable def preparePacking {n : ℕ} (i : TerminalLotto n)
    (lengths resources : FixedArrayTable n ℝ)
    (hL : lengths.read = i.length) (hR : resources.read = i.resource) : Run (ClassifiedPacking i) := by
  let indices := indexList n
  let classified := classify lengths resources indices.value
  have hMembers : classified.value.1 = i.uniformItems := by
    simp only [classified, classify_value, indices, indexList_value, hL, hR]
    rfl
  have hPivot : classified.value.2 = i.realPivot := by
    simp only [classified, classify_value, indices, indexList_value, hL, hR]
    unfold TerminalLotto.realPivot
    apply congrArg (fun predicate => (List.finRange n).find? predicate)
    funext j
    apply congrArg (fun dec : Decidable (Fractional i.length i.resource j) => @decide _ dec)
    exact Subsingleton.elim _ _
  let budget : Run ℝ := ⟨i.B, [.load 0 i.B]⟩
  let packed := RealPRGPackingExecution.packedGroups lengths budget.value classified.value.1
  have hGroups : packed.value.map Prod.fst = i.groups := by
    simp only [packed, budget, RealPRGPackingExecution.packedGroups_value, hL, hMembers,
      realPackedGroups_groups]
    rfl
  have hCount : packed.value.length = i.groups.length := by
    have h := congrArg List.length hGroups
    simpa only [List.length_map] using h
  let count := listLength packed.value
  let array := listArray packed.value count.value (listLength_value packed.value)
  let table : FixedArrayTable i.groups.length (List (Fin n) × ℝ) :=
    ⟨array.value.data, array.value.size.trans ((listLength_value packed.value).trans hCount)⟩
  have hRead : ∀ g : Fin i.groups.length, table.read g =
      packed.value.get ⟨g.val, by rw [hCount]; exact g.isLt⟩ := by
    intro g
    have ht := listArray_read packed.value count.value (listLength_value packed.value)
      ⟨g.val, by rw [listLength_value, hCount]; exact g.isLt⟩
    exact ht
  have hPacking : ∀ g : Fin i.groups.length, (table.read g).1 = i.groups.get g := by
    intro g
    rw [hRead]
    have he := List.getElem_of_eq hGroups (by rw [hGroups]; exact g.isLt)
    rw [List.getElem_map] at he
    exact he
  have hTotal : ∀ g : Fin i.groups.length, (table.read g).2 = i.partition.total g := by
    intro g
    have hNative : packed.value = realPackedGroups i.length i.B i.uniformItems := by
      simp only [packed, budget, RealPRGPackingExecution.packedGroups_value, hL, hMembers]
    have hMem : table.read g ∈ packed.value := by
      rw [hRead]
      exact List.get_mem _ _
    rw [hNative] at hMem
    have h := realPackedGroups_totals i.length i.B i.uniformItems (table.read g) hMem
    rw [h, hPacking]
    exact (packingPartition_total i.length i.length_pos i.B i.uniformItems i.uniformItems_nodup
      (fun j _ => i.length_le j) g).symm
  exact ⟨⟨⟨table, hPacking, hTotal⟩, classified.value.2, hPivot⟩,
    indices.trace ++ classified.trace ++ budget.trace ++ packed.trace ++ count.trace ++ array.trace ++
      [.control, .storeCell 0, .storeCell 1]⟩


theorem preparePacking_cost {n : ℕ} (i : TerminalLotto n)
    (lengths resources : FixedArrayTable n ℝ)
    (hL : lengths.read = i.length) (hR : resources.read = i.resource) :
    (preparePacking i lengths resources hL hR).cost ≤ 40 * n + 60 := by
  let indices := indexList n
  let classified := classify lengths resources indices.value
  let packed := RealPRGPackingExecution.packedGroups lengths i.B classified.value.1
  have hMembers : classified.value.1 = i.uniformItems := by
    simp only [classified, classify_value, indices, indexList_value, hL, hR]
    rfl
  have hGroups : packed.value.map Prod.fst = i.groups := by
    simp only [packed, RealPRGPackingExecution.packedGroups_value, hL, hMembers,
      realPackedGroups_groups]
    rfl
  have hCount : packed.value.length = i.groups.length := by
    have h := congrArg List.length hGroups
    simpa only [List.length_map] using h
  have hSmall : packed.value.length ≤ 3 := hCount.trans_le i.groups_count_upper
  have hItems : classified.value.1.length ≤ n := by
    rw [hMembers]
    exact (List.length_filter_le _ _).trans_eq (List.length_finRange (n := n))
  have hIndices := indexList_cost n
  have hClassified : classified.cost ≤ 16 * n + 1 := by
    have h := classify_cost lengths resources indices.value
    simpa only [classified, indices, indexList_value, List.length_finRange] using h
  have hPacked := RealPRGPackingExecution.packedGroups_cost lengths i.B classified.value.1
  change packed.cost ≤ _ at hPacked
  change indices.cost = _ at hIndices
  have hLength := listLength_cost packed.value
  have hArray := listArray_cost packed.value (listLength packed.value).value (listLength_value packed.value)
  have hSmallValue : (listLength packed.value).value ≤ 3 := by rw [listLength_value]; exact hSmall
  have hArrayBound : (listArray packed.value (listLength packed.value).value
      (listLength_value packed.value)).cost ≤ 29 := hArray.trans
      (Nat.add_le_add_left (Nat.mul_le_mul hSmallValue (by omega :
        2 * (listLength packed.value).value + 3 ≤ 2 * 3 + 3)) 2)
  unfold preparePacking
  change cost (indices.trace ++ classified.trace ++ [.load 0 i.B] ++ packed.trace ++
    (listLength packed.value).trace ++
    (listArray packed.value (listLength packed.value).value (listLength_value packed.value)).trace ++
      [.control, .storeCell 0, .storeCell 1]) ≤ _
  simp only [cost_append]
  change indices.cost + classified.cost + 1 + packed.cost + (listLength packed.value).cost +
    (listArray packed.value (listLength packed.value).value (listLength_value packed.value)).cost + 3 ≤ _
  rw [hIndices, hLength]
  omega



structure RouteState (n m : ℕ) where
  tags : PairStoreBuffer n (Option (Fin m))
  coefficients : PairStoreBuffer n ℝ

inductive RouteInstruction (n m : ℕ) where
  | store (cell : Fin n) (tag : Option (Fin m)) (coefficient : ℝ)

namespace RouteInstruction

def execute {n m : ℕ} : RouteInstruction n m → RouteState n m → RouteState n m
  | .store j tag coefficient, state =>
      ⟨state.tags.write j tag, state.coefficients.write j coefficient⟩

theorem regions {n m : ℕ} (instruction : RouteInstruction n m) (state : RouteState n m) :
    (instruction.execute state).tags.data.size = n ∧
      (instruction.execute state).coefficients.data.size = n :=
  ⟨(instruction.execute state).tags.size, (instruction.execute state).coefficients.size⟩

theorem addresses_disjoint {n : ℕ} (tag coefficient : Fin n) :
    tag.val ≠ n + coefficient.val := by have h := tag.isLt; omega

end RouteInstruction

noncomputable def routeView {n m : ℕ} (state : RouteState n m) : FixedArrayTable n (RealGroupRoute m) :=
  FixedArrayTable.ofFn (fun j => (state.tags.read j, state.coefficients.read j))

noncomputable def routeStore {n m : ℕ} (state : RouteState n m) (j : Fin n)
    (tag : Option (Fin m)) (coefficient : ℝ) : Run (RouteState n m) :=
  ⟨(RouteInstruction.store j tag coefficient).execute state,
    [.storeCell j.val, .store (n + j.val) coefficient, .control]⟩

theorem routeStore_cost {n m : ℕ} (state : RouteState n m) (j : Fin n)
    (tag : Option (Fin m)) (coefficient : ℝ) : (routeStore state j tag coefficient).cost = 3 := rfl

theorem routeStore_view {n m : ℕ} (state : RouteState n m) (j : Fin n)
    (tag : Option (Fin m)) (coefficient : ℝ) :
    routeView (routeStore state j tag coefficient).value = (routeView state).write j (tag, coefficient) := by
  apply table_ext
  intro k
  simp only [routeStore, RouteInstruction.execute, routeView, FixedArrayTable.read_ofFn,
    FixedArrayTable.read_write, PairStoreBuffer.read_write]
  by_cases h : k = j <;> simp [h]

noncomputable def initialRoutes (n m : ℕ) : Run (RouteState n m) :=
  let tags := arrayRun n (fun _ => (⟨none, [.control]⟩ : Run (Option (Fin m))))
  let coefficients := arrayRun n (fun _ => (⟨0, [.load 0 0]⟩ : Run ℝ))
  ⟨⟨⟨tags.value.data, tags.value.size⟩, ⟨coefficients.value.data, coefficients.value.size⟩⟩,
    tags.trace ++ coefficients.trace ++ [.storeCell 0, .storeCell 1, .control, .control]⟩

theorem initialRoutes_view (n m : ℕ) :
    routeView (initialRoutes n m).value = FixedArrayTable.ofFn (fun _ => (none, 0)) := by
  apply table_ext
  intro j
  simp [routeView, initialRoutes, arrayRun, FixedArrayTable.ofFn, PairStoreBuffer.read,
    FixedArrayTable.read]

theorem initialRoutes_cost (n m : ℕ) : (initialRoutes n m).cost = 6 * n + 8 := by
  unfold initialRoutes
  change cost (_ ++ _ ++ _) = _
  simp only [cost_append]
  change (arrayRun n _).cost + (arrayRun n _).cost + 4 = _
  rw [arrayRun_cost, arrayRun_cost]
  simp [Run.cost, Operation.cost]
  omega

noncomputable def storeMembers {n m : ℕ} (lengths : FixedArrayTable n ℝ) (g : Fin m) (total : ℝ) :
    List (Fin n) → RouteState n m → Run (RouteState n m)
  | [], state => ⟨state, [.control]⟩
  | j :: rest, state =>
      let length := loadReal lengths j
      let available : Run ℝ := ⟨total, [.load (2 * n) total]⟩
      let coefficient := arithmetic .div length.value available.value
      let stored := routeStore state j (some g) coefficient.value
      let later := storeMembers lengths g total rest stored.value
      ⟨later.value, length.trace ++ available.trace ++ coefficient.trace ++ stored.trace ++
        [.control, .control] ++ later.trace⟩

theorem storeMembers_cost {n m : ℕ} (lengths : FixedArrayTable n ℝ) (g : Fin m) (total : ℝ)
    (members : List (Fin n)) (state : RouteState n m) :
    (storeMembers lengths g total members state).cost = 8 * members.length + 1 := by
  induction members generalizing state with
  | nil => rfl
  | cons j rest ih =>
      unfold storeMembers
      change cost (_ ++ _ ++ _ ++ _ ++ _ ++ _) = _
      simp only [cost_append]
      change 1 + 1 + 1 + 3 + 2 +
        (storeMembers lengths g total rest
          (routeStore state j (some g) (lengths.read j / total)).value).cost = _
      rw [ih, List.length_cons]
      omega

theorem storeMembers_view {n m : ℕ} (lengths : FixedArrayTable n ℝ) (g : Fin m) (total : ℝ)
    (members : List (Fin n)) (state : RouteState n m) :
    routeView (storeMembers lengths g total members state).value =
      (routeView state).patch (members.map (fun j => (j, (some g, lengths.read j / total)))) := by
  induction members generalizing state with
  | nil => rfl
  | cons j rest ih =>
      simp only [storeMembers, loadReal, arithmetic, Operation.realValue, RealArithmeticOp.apply,
        List.map_cons, FixedArrayTable.patch]
      rw [ih, routeStore_view]

theorem patch_append {n : ℕ} {α : Type*} (table : FixedArrayTable n α)
    (first second : List (Fin n × α)) :
    table.patch (first ++ second) = (table.patch first).patch second := by
  induction first generalizing table with
  | nil => rfl
  | cons head rest ih => simp only [List.cons_append, FixedArrayTable.patch, ih]

noncomputable def storeGroups {n m : ℕ} (lengths : FixedArrayTable n ℝ)
    (groups : FixedArrayTable m (List (Fin n) × ℝ)) (totals : FixedArrayTable m ℝ) :
    List (Fin m) → RouteState n m → Run (RouteState n m)
  | [], state => ⟨state, [.control]⟩
  | g :: rest, state =>
      let members := (groups.read g).1
      let total := loadReal totals g
      let selected := storeMembers lengths g total.value members state
      let later := storeGroups lengths groups totals rest selected.value
      ⟨later.value, [.control] ++ total.trace ++ selected.trace ++ [.control, .control] ++ later.trace⟩

theorem storeGroups_view {n m : ℕ} (lengths : FixedArrayTable n ℝ)
    (groups : FixedArrayTable m (List (Fin n) × ℝ)) (totals : FixedArrayTable m ℝ)
    (indices : List (Fin m)) (state : RouteState n m) :
    routeView (storeGroups lengths groups totals indices state).value =
      (routeView state).patch (indices.flatMap (fun g => (groups.read g).1.map
        (fun j => (j, (some g, lengths.read j / totals.read g))))) := by
  induction indices generalizing state with
  | nil => rfl
  | cons g rest ih =>
      simp only [storeGroups, loadReal, Operation.realValue, List.flatMap_cons]
      rw [ih, storeMembers_view, patch_append]

theorem storeGroups_cost {n m : ℕ} (lengths : FixedArrayTable n ℝ)
    (groups : FixedArrayTable m (List (Fin n) × ℝ)) (totals : FixedArrayTable m ℝ)
    (indices : List (Fin m)) (state : RouteState n m) :
    (storeGroups lengths groups totals indices state).cost =
      8 * (indices.flatMap (fun g => (groups.read g).1)).length + 5 * indices.length + 1 := by
  induction indices generalizing state with
  | nil => rfl
  | cons g rest ih =>
      unfold storeGroups
      change cost (_ ++ _ ++ _ ++ _ ++ _) = _
      simp only [cost_append]
      change 1 + 1 + (storeMembers lengths g (totals.read g) (groups.read g).1 state).cost + 2 +
        (storeGroups lengths groups totals rest _).cost = _
      rw [storeMembers_cost, ih]
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega

noncomputable def materializeRoutes {n m : ℕ} (state : RouteState n m) :
    Run (FixedArrayTable n (RealGroupRoute m)) :=
  arrayRun n (fun j =>
    let coefficient : Run ℝ := ⟨state.coefficients.read j, [.load (n + j.val) (state.coefficients.read j)]⟩
    ⟨(state.tags.read j, coefficient.value), [.control] ++ coefficient.trace ++
      [.storeCell (2 * n + j.val), .store (3 * n + j.val) coefficient.value]⟩)

theorem materializeRoutes_value {n m : ℕ} (state : RouteState n m) :
    (materializeRoutes state).value = routeView state := by
  apply table_ext
  intro j
  simp [materializeRoutes, arrayRun_read, routeView, FixedArrayTable.read_ofFn]

theorem materializeRoutes_cost {n m : ℕ} (state : RouteState n m) :
    (materializeRoutes state).cost = 6 * n + 2 := by
  unfold materializeRoutes
  rw [arrayRun_cost]
  simp [Run.cost, Operation.cost, Nat.mul_comm]
  omega

noncomputable def totalsArray {n m : ℕ} (groups : FixedArrayTable m (List (Fin n) × ℝ)) :
    Run (FixedArrayTable m ℝ) := by
  let count := groups.data.size
  let values := arrayRun count (fun j =>
    let source := groups.read (j.cast groups.size)
    (⟨source.2, [.control, .load j.val source.2]⟩ : Run ℝ))
  exact ⟨⟨values.value.data, values.value.size.trans groups.size⟩,
    [.control] ++ values.trace ++ [.storeCell 0]⟩

theorem totalsArray_read {n m : ℕ} (groups : FixedArrayTable m (List (Fin n) × ℝ)) (g : Fin m) :
    (totalsArray groups).value.read g = (groups.read g).2 := by
  unfold totalsArray
  have h := arrayRun_read groups.data.size
    (fun j => (⟨(groups.read (j.cast groups.size)).2,
      [.control, .load j.val (groups.read (j.cast groups.size)).2]⟩ : Run ℝ))
    (g.cast groups.size.symm)
  exact h

theorem totalsArray_cost {n m : ℕ} (groups : FixedArrayTable m (List (Fin n) × ℝ)) :
    (totalsArray groups).cost = 4 * m + 4 := by
  unfold totalsArray
  change cost (_ ++ _ ++ _) = _
  simp only [cost_append]
  change 1 + (arrayRun groups.data.size _).cost + 1 = _
  rw [arrayRun_cost]
  simp [Run.cost, Operation.cost, groups.size]
  omega



noncomputable def castRoutes {n m k : ℕ} (h : m = k) (table : FixedArrayTable n (RealGroupRoute m)) :
    FixedArrayTable n (RealGroupRoute k) := h ▸ table

noncomputable def routePreparationCore {n m : ℕ} (lengths : FixedArrayTable n ℝ)
    (groups : FixedArrayTable m (List (Fin n) × ℝ)) (totals : FixedArrayTable m ℝ) :
    Run (FixedArrayTable n (RealGroupRoute m)) := by
  let count := groups.data.size
  let indices := indexList count
  let nativeGroups : FixedArrayTable count (List (Fin n) × ℝ) := ⟨groups.data, rfl⟩
  let nativeTotals : FixedArrayTable count ℝ := ⟨totals.data, totals.size.trans groups.size.symm⟩
  let initial := initialRoutes n count
  let written := storeGroups lengths nativeGroups nativeTotals indices.value initial.value
  let materialized := materializeRoutes written.value
  exact ⟨castRoutes groups.size materialized.value,
    [.control, .storeCell 0, .storeCell 1] ++ indices.trace ++ initial.trace ++ written.trace ++
      materialized.trace ++ [.control, .storeCell 0]⟩

theorem routePreparationCore_value {n m : ℕ} (lengths : FixedArrayTable n ℝ)
    (groups : FixedArrayTable m (List (Fin n) × ℝ)) (totals : FixedArrayTable m ℝ) :
    (routePreparationCore lengths groups totals).value =
      (FixedArrayTable.ofFn (fun _ => (none, 0))).patch ((List.finRange m).flatMap
        (fun g => (groups.read g).1.map (fun j => (j, (some g, lengths.read j / totals.read g))))) := by
  cases groups with
  | mk data size =>
      cases size
      simp only [routePreparationCore, castRoutes, materializeRoutes_value, storeGroups_view,
        initialRoutes_view, indexList_value]

theorem routePreparationCore_cost {n m : ℕ} (lengths : FixedArrayTable n ℝ)
    (groups : FixedArrayTable m (List (Fin n) × ℝ)) (totals : FixedArrayTable m ℝ) :
    (routePreparationCore lengths groups totals).cost =
      12 * n + 8 * ((List.finRange m).flatMap (fun g => (groups.read g).1)).length + 10 * m + 19 := by
  cases groups with
  | mk data size =>
      cases size
      unfold routePreparationCore
      change cost (_ ++ _ ++ _ ++ _ ++ _ ++ _) = _
      simp only [cost_append]
      change 3 + (indexList data.size).cost + (initialRoutes n data.size).cost +
        (storeGroups lengths ⟨data, rfl⟩ totals (indexList data.size).value (initialRoutes n data.size).value).cost +
        (materializeRoutes _).cost + 2 = _
      rw [indexList_cost, initialRoutes_cost, storeGroups_cost, materializeRoutes_cost,
        indexList_value, List.length_finRange]
      omega

noncomputable def routePreparation {n : ℕ} (i : TerminalLotto n)
    (lengths : FixedArrayTable n ℝ) (hL : lengths.read = i.length)
    (packing : RealTerminalPacking i) : Run (RealPreparedGroupOutput i.partition) := by
  let totals := totalsArray packing.groups
  let routes := routePreparationCore lengths packing.groups totals.value
  have hTotals : ∀ g, totals.value.read g = i.partition.total g := by
    intro g
    rw [totalsArray_read]
    exact packing.total_correct g
  have hActual : routes.value = (FixedArrayTable.ofFn (fun _ => (none, 0))).patch
      (packing.routeAssignments totals.value) := by
    rw [routePreparationCore_value]
    simp only [RealTerminalPacking.routeAssignments, hL]
  have hTable : ∀ j, routes.value.read j = (i.partition.realRoutes totals.value).read j := by
    have hT : totals.value = (packing.prepareOutput).totals := by
      apply table_ext
      intro g
      change totals.value.read g = (FixedArrayTable.ofFn (fun g => (packing.groups.read g).2)).read g
      rw [FixedArrayTable.read_ofFn]
      exact totalsArray_read packing.groups g
    intro j
    rw [hActual, hT]
    exact (packing.prepareOutput).table_correct j
  exact ⟨⟨totals.value, hTotals, routes.value, hTable⟩,
    totals.trace ++ routes.trace ++ [.control, .storeCell 0, .storeCell 1]⟩

theorem routePreparation_cost {n : ℕ} (i : TerminalLotto n)
    (lengths : FixedArrayTable n ℝ) (hL : lengths.read = i.length)
    (packing : RealTerminalPacking i) :
    (routePreparation i lengths hL packing).cost ≤ 20 * n + 70 := by
  let totals := totalsArray packing.groups
  have hIndices : ((List.finRange i.groups.length).flatMap (fun g => (packing.groups.read g).1)).length ≤ n := by
    have he := packing.routeAssignments_length_le totals.value
    simpa only [RealTerminalPacking.routeAssignments, List.length_flatMap,
      List.length_map, Function.comp_def] using he
  have hGroups := i.groups_count_upper
  have ht := totalsArray_cost packing.groups
  have hr := routePreparationCore_cost lengths packing.groups totals.value
  unfold routePreparation
  change cost (_ ++ _ ++ _) ≤ _
  simp only [cost_append]
  change (totalsArray packing.groups).cost +
    (routePreparationCore lengths packing.groups totals.value).cost + 3 ≤ _
  rw [ht, hr]
  omega



structure Prepared {n : ℕ} (i : TerminalLotto n) where
  output : RealPreparedGroupOutput i.partition
  pivot : Option (Fin n)
  pivot_correct : pivot = i.realPivot
  budget : ℝ
  budget_correct : budget = i.B
  ell : ℝ
  probability : ℝ
  ell_correct : ∀ j, pivot = some j → ell = i.length j
  probability_correct : ∀ j, pivot = some j → probability = i.resource j / i.length j

noncomputable def prepare {n : ℕ} (i : TerminalLotto n) (lengths resources : FixedArrayTable n ℝ)
    (hL : lengths.read = i.length) (hR : resources.read = i.resource) : Run (Prepared i) := by
  let packed := preparePacking i lengths resources hL hR
  let output := routePreparation i lengths hL packed.value.packing
  let budget : Run ℝ := ⟨i.B, [.load 0 i.B]⟩
  match hp : packed.value.pivot with
  | none =>
      exact ⟨⟨output.value, none, hp.symm.trans packed.value.pivot_correct,
        budget.value, rfl, 0, 0,
        (by intro j h; cases h), (by intro j h; cases h)⟩,
        packed.trace ++ output.trace ++ budget.trace ++ [.load 0 0, .load 0 0] ++
          [.storeCell 0, .storeCell 1, .storeCell 2, .storeCell 3, .storeCell 4, .control, .control]⟩
  | some j =>
      let length := loadReal lengths j
      let resource := loadReal resources j
      let probability := arithmetic .div resource.value length.value
      exact ⟨⟨output.value, some j, hp.symm.trans packed.value.pivot_correct,
        budget.value, rfl, length.value, probability.value,
        (by intro k h; cases Option.some.inj h; exact congrFun hL j),
        (by intro k h; cases Option.some.inj h; simp only [probability, resource, length, loadReal,
          arithmetic, Operation.realValue, RealArithmeticOp.apply, hL, hR])⟩,
        packed.trace ++ output.trace ++ budget.trace ++ length.trace ++ resource.trace ++ probability.trace ++
          [.storeCell 0, .storeCell 1, .storeCell 2, .storeCell 3, .storeCell 4, .control, .control]⟩

theorem prepare_cost {n : ℕ} (i : TerminalLotto n) (lengths resources : FixedArrayTable n ℝ)
    (hL : lengths.read = i.length) (hR : resources.read = i.resource) :
    (prepare i lengths resources hL hR).cost ≤ 60 * n + 150 := by
  have hp := preparePacking_cost i lengths resources hL hR
  have hr := routePreparation_cost i lengths hL (preparePacking i lengths resources hL hR).value.packing
  unfold prepare
  dsimp only
  split
  · change cost (_ ++ _ ++ _ ++ _ ++ _) ≤ _
    simp only [cost_append]
    change (preparePacking i lengths resources hL hR).cost +
      (routePreparation i lengths hL (preparePacking i lengths resources hL hR).value.packing).cost + 1 + 2 + 7 ≤ _
    omega
  · change cost (_ ++ _ ++ _ ++ _ ++ _ ++ _ ++ _) ≤ _
    simp only [cost_append]
    change (preparePacking i lengths resources hL hR).cost +
      (routePreparation i lengths hL (preparePacking i lengths resources hL hR).value.packing).cost + 1 + 1 + 1 + 1 + 7 ≤ _
    omega

noncomputable def drawPrepared {n : ℕ} {i : TerminalLotto n} (prepared : Prepared i)
    (seed : RealFourSeed) : Run (FixedArrayTable n ℝ) := by
  match hp : prepared.pivot with
  | none =>
      have hNo : ∀ j, ¬Fractional i.length i.resource j :=
        i.realPivot_none.mp (prepared.pivot_correct.symm.trans hp)
      let spec := prepared.output.uniformSpec hNo
      let small := RealPRGGroupExecution.uniformDraw spec i.groups_count prepared.output.totals rfl
        prepared.budget prepared.budget_correct seed
      exact join (⟨(), [.control]⟩ : Run Unit)
        (join small (RealPRGPackingExecution.emit prepared.output.table small.value))
  | some pivot =>
      have hFractional : Fractional i.length i.resource pivot :=
        i.realPivot_some (prepared.pivot_correct.symm.trans hp)
      let spec := prepared.output.mixedSpec pivot hFractional
      let small := RealPRGGroupExecution.mixedDraw spec i.groups_count prepared.output.totals rfl
        prepared.budget prepared.ell prepared.probability prepared.budget_correct
        (prepared.ell_correct pivot hp) (prepared.probability_correct pivot hp) seed
      exact join (⟨(), [.control]⟩ : Run Unit)
        (join small (RealPRGPackingExecution.emitMixedCached prepared.output.table small.value pivot))

theorem drawPrepared_value {n : ℕ} {i : TerminalLotto n} (prepared : Prepared i)
    (seed : RealFourSeed) : (drawPrepared prepared seed).value.read = i.realSample seed := by
  unfold drawPrepared
  dsimp only
  split
  · rename_i hp
    have hNo := i.realPivot_none.mp (prepared.pivot_correct.symm.trans hp)
    simp only [join_value, RealPRGPackingExecution.emit_value, RealPreparedGroupOutput.emit_allocation,
      RealPRGGroupExecution.uniformDraw_value, RealPreparedGroupOutput.uniformSpec_eq]
    rw [i.realSample_eq_uniform hNo]
    exact (i.realUniformSample_eq_split hNo seed).symm
  · rename_i pivot hp
    have hFractional := i.realPivot_some (prepared.pivot_correct.symm.trans hp)
    simp only [join_value, RealPRGPackingExecution.emitMixedCached_value, RealPreparedGroupOutput.emitMixed_allocation,
      RealPRGGroupExecution.mixedDraw_value, RealPreparedGroupOutput.mixedSpec_eq]
    rw [i.realSample_eq_mixed pivot hFractional]
    exact (i.realMixedSample_eq_split pivot hFractional seed).symm

theorem drawPrepared_cost {n : ℕ} {i : TerminalLotto n} (prepared : Prepared i)
    (seed : RealFourSeed) : (drawPrepared prepared seed).cost ≤ 14 * n + 428010 := by
  unfold drawPrepared
  dsimp only
  split
  · rename_i hp
    rw [join_cost, join_cost]
    have hs := RealPRGGroupExecution.uniformDraw_cost
      (prepared.output.uniformSpec (i.realPivot_none.mp (prepared.pivot_correct.symm.trans hp)))
      i.groups_count prepared.output.totals rfl prepared.budget prepared.budget_correct seed
    have he := RealPRGPackingExecution.emit_cost prepared.output.table
      (RealPRGGroupExecution.uniformDraw
        (prepared.output.uniformSpec (i.realPivot_none.mp (prepared.pivot_correct.symm.trans hp)))
        i.groups_count prepared.output.totals rfl prepared.budget prepared.budget_correct seed).value
    change 1 + (_ + _) ≤ _
    omega
  · rename_i pivot hp
    rw [join_cost, join_cost]
    have hs := RealPRGGroupExecution.mixedDraw_cost
      (prepared.output.mixedSpec pivot (i.realPivot_some (prepared.pivot_correct.symm.trans hp)))
      i.groups_count prepared.output.totals rfl prepared.budget prepared.ell prepared.probability
      prepared.budget_correct (prepared.ell_correct pivot hp) (prepared.probability_correct pivot hp) seed
    have he := RealPRGPackingExecution.emitMixedCached_cost prepared.output.table
      (RealPRGGroupExecution.mixedDraw
        (prepared.output.mixedSpec pivot (i.realPivot_some (prepared.pivot_correct.symm.trans hp)))
        i.groups_count prepared.output.totals rfl prepared.budget prepared.ell prepared.probability prepared.budget_correct
        (prepared.ell_correct pivot hp) (prepared.probability_correct pivot hp) seed).value pivot
    change 1 + (_ + _) ≤ _
    omega

noncomputable def draw {n : ℕ} (i : TerminalLotto n) (lengths resources : FixedArrayTable n ℝ)
    (hL : lengths.read = i.length) (hR : resources.read = i.resource)
    (seed : RealFourSeed) : Run (FixedArrayTable n ℝ) :=
  let prepared := prepare i lengths resources hL hR
  join prepared (drawPrepared prepared.value seed)

theorem draw_value {n : ℕ} (i : TerminalLotto n) (lengths resources : FixedArrayTable n ℝ)
    (hL : lengths.read = i.length) (hR : resources.read = i.resource)
    (seed : RealFourSeed) : (draw i lengths resources hL hR seed).value.read = i.realSample seed :=
  drawPrepared_value _ _

theorem draw_cost {n : ℕ} (i : TerminalLotto n) (lengths resources : FixedArrayTable n ℝ)
    (hL : lengths.read = i.length) (hR : resources.read = i.resource)
    (seed : RealFourSeed) : (draw i lengths resources hL hR seed).cost ≤ 74 * n + 428160 := by
  rw [draw, join_cost]
  have hp := prepare_cost i lengths resources hL hR
  have hd := drawPrepared_cost (prepare i lengths resources hL hR).value seed
  omega

theorem draw_law {n : ℕ} (i : TerminalLotto n) (lengths resources : FixedArrayTable n ℝ)
    (hL : lengths.read = i.length) (hR : resources.read = i.resource) :
    Measure.map (fun seed => (draw i lengths resources hL hR seed).value.read)
      (FourInput.realInputLaw : Measure RealFourSeed) = (i.law : Measure (Allocation n)) := by
  have h : (fun seed => (draw i lengths resources hL hR seed).value.read) = i.realSample :=
    funext (draw_value i lengths resources hL hR)
  rw [h]
  exact i.realSample_law

theorem draw_fullBudget {n : ℕ} (i : TerminalLotto n) (lengths resources : FixedArrayTable n ℝ)
    (hL : lengths.read = i.length) (hR : resources.read = i.resource)
    (seed : RealFourSeed) (hs : realGroupSeedValid seed) :
    FullBudget i.B (draw i lengths resources hL hR seed).value.read := by
  rw [draw_value]
  exact i.realSample_fullBudget seed hs


end Blotto.RealPRGTerminalExecution
