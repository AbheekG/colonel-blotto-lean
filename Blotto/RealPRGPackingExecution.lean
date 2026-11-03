import Blotto.PRGRealRAMExecution
import Blotto.RealPackedGroups
import Blotto.RealRawGroupRouting

/-! Named real-RAM execution of the actual next-fit packing spine and cached
coordinate emission. List inspection, link construction and loop advance use
unit control/cell operations; scalar loads, arithmetic and comparisons use the
same explicit RAM model as the local sampler. These derived execution bounds
do not price producing the incoming length array or the terminal classifier. -/

namespace Blotto.RealPRGPackingExecution
open PRGRealRAMExecution PRGExactRealRAMContract
open scoped BigOperators Classical

def reverseAux {α : Type*} : List α → List α → Run (List α)
  | [], acc => ⟨acc, [.control]⟩
  | x :: rest, acc =>
      let later := reverseAux rest (x :: acc)
      ⟨later.value, [.control, .control, .storeCell 0, .control] ++ later.trace⟩

theorem reverseAux_value {α : Type*} (items acc : List α) :
    (reverseAux items acc).value = items.reverse ++ acc := by
  induction items generalizing acc with
  | nil => rfl
  | cons x rest ih => simp [reverseAux, ih, List.reverse_cons, List.append_assoc]

theorem reverseAux_cost {α : Type*} (items acc : List α) :
    (reverseAux items acc).cost = 4 * items.length + 1 := by
  induction items generalizing acc with
  | nil => rfl
  | cons x rest ih =>
      change cost ([.control, .control, .storeCell 0, .control] ++ _) = _
      rw [cost_append]
      change 4 + (reverseAux rest (x :: acc)).cost = _
      rw [ih, List.length_cons]
      omega

noncomputable def packAux {n : ℕ} (lengths : FixedArrayTable n ℝ) (B : ℝ) :
    List (Fin n) → ℝ → List (Fin n) → Run (List (List (Fin n) × ℝ))
  | current, s, [] =>
      let members := reverseAux current []
      ⟨[(members.value, s)], members.trace ++ [.storeCell 0, .storeCell 1, .control, .control]⟩
  | current, s, x :: rest =>
      let item := loadReal lengths x
      let next := arithmetic .add s item.value
      let guard := compareLe next.value B
      let visited :=  [.control] ++ item.trace ++ next.trace ++ guard.trace ++ [.control]
      if guard.value then
        let later := packAux lengths B (x :: current) next.value rest
        ⟨later.value, visited ++ [.storeCell x.val, .control] ++ later.trace⟩
      else
        let members := reverseAux current []
        let later := packAux lengths B [x] item.value rest
        ⟨(members.value, s) :: later.value,
          visited ++ members.trace ++ [.storeCell 0, .storeCell 1, .control] ++
            [.storeCell x.val, .control] ++ later.trace⟩

theorem packAux_value {n : ℕ} (lengths : FixedArrayTable n ℝ) (B : ℝ)
    (current : List (Fin n)) (s : ℝ) (rest : List (Fin n)) :
    (packAux lengths B current s rest).value = realPackSumsAux lengths.read B current s rest := by
  induction rest generalizing current s with
  | nil => simp [packAux, realPackSumsAux, reverseAux_value]
  | cons x rest ih =>
      simp only [packAux, loadReal, arithmetic, Operation.realValue,
        RealArithmeticOp.apply, compareLe, realPackSumsAux]
      by_cases h : s + lengths.read x ≤ B
      · simp [h, ih]
      · simp [h, reverseAux_value, ih]

theorem packAux_cost {n : ℕ} (lengths : FixedArrayTable n ℝ) (B : ℝ)
    (current : List (Fin n)) (s : ℝ) (rest : List (Fin n)) :
    (packAux lengths B current s rest).cost ≤ 16 * rest.length + 4 * current.length + 5 := by
  induction rest generalizing current s with
  | nil =>
      change cost ((reverseAux current []).trace ++ _) ≤ _
      rw [cost_append]
      change (reverseAux current []).cost + 4 ≤ _
      rw [reverseAux_cost]
      simp
  | cons x rest ih =>
      unfold packAux
      dsimp only
      split
      · have h := ih (x :: current) (s + lengths.read x)
        change cost (_ ++ _ ++ (packAux lengths B (x :: current) (s + lengths.read x) rest).trace) ≤ _
        simp only [cost_append]
        change 5 + 2 + (packAux lengths B (x :: current) (s + lengths.read x) rest).cost ≤ _
        simp only [List.length_cons] at h ⊢
        omega
      · have h := ih [x] (lengths.read x)
        change cost (_ ++ (reverseAux current []).trace ++ _ ++ _ ++
          (packAux lengths B [x] (lengths.read x) rest).trace) ≤ _
        simp only [cost_append]
        change 5 + (reverseAux current []).cost + 3 + 2 +
          (packAux lengths B [x] (lengths.read x) rest).cost ≤ _
        rw [reverseAux_cost]
        simp only [List.length_cons, List.length_nil] at h ⊢
        omega

noncomputable def packedGroups {n : ℕ} (lengths : FixedArrayTable n ℝ) (B : ℝ) :
    List (Fin n) → Run (List (List (Fin n) × ℝ))
  | [] => ⟨[], [.control]⟩
  | x :: rest =>
      let first := loadReal lengths x
      let later := packAux lengths B [x] first.value rest
      ⟨later.value, [.control, .storeCell 0] ++ first.trace ++ later.trace⟩

theorem packedGroups_value {n : ℕ} (lengths : FixedArrayTable n ℝ) (B : ℝ)
    (items : List (Fin n)) :
    (packedGroups lengths B items).value = realPackedGroups lengths.read B items := by
  cases items with
  | nil => rfl
  | cons x rest => exact packAux_value lengths B [x] (lengths.read x) rest

theorem packedGroups_cost {n : ℕ} (lengths : FixedArrayTable n ℝ) (B : ℝ)
    (items : List (Fin n)) : (packedGroups lengths B items).cost ≤ 16 * items.length + 5 := by
  cases items with
  | nil => simp [packedGroups, Run.cost, Operation.cost]
  | cons x rest =>
      have h := packAux_cost lengths B [x] (lengths.read x) rest
      change cost (_ ++ (packAux lengths B [x] (lengths.read x) rest).trace) ≤ _
      rw [cost_append]
      change 3 + (packAux lengths B [x] (lengths.read x) rest).cost ≤ _
      simp only [List.length_cons, List.length_nil] at h ⊢
      omega

noncomputable def routedCell {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable m ℝ) (j : Fin n) : Run ℝ :=
  let route := routes.read j
  match route.1 with
  | none => ⟨0, [.control, .control, .control, .load 0 0]⟩
  | some g =>
      let coefficient : Run ℝ := ⟨route.2, [.load j.val route.2]⟩
      let value := loadReal sampled g
      let result := arithmetic .mul coefficient.value value.value
      ⟨result.value, [.control, .control, .control] ++ coefficient.trace ++ value.trace ++ result.trace⟩

theorem routedCell_value {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable m ℝ) (j : Fin n) :
    (routedCell routes sampled j).value =
      match (routes.read j).1 with
      | none => 0
      | some g => (routes.read j).2 * sampled.read g := by
  cases h : (routes.read j).1 <;> simp [routedCell, h, loadReal, arithmetic,
    Operation.realValue, RealArithmeticOp.apply]

theorem routedCell_cost {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable m ℝ) (j : Fin n) : (routedCell routes sampled j).cost ≤ 6 := by
  cases h : (routes.read j).1 <;> simp [routedCell, h, Run.cost, loadReal, arithmetic, Operation.cost]

noncomputable def emit {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable m ℝ) : Run (FixedArrayTable n ℝ) :=
  arrayRun n (routedCell routes sampled)

theorem emit_value {n m : ℕ} {G : ProportionalGroups n m} (p : RealPreparedGroupOutput G)
    (sampled : FixedArrayTable m ℝ) :
    (emit p.table sampled).value = p.emit sampled.read := by
  apply table_ext
  intro j
  simp only [emit, arrayRun_read, routedCell_value, RealPreparedGroupOutput.emit,
    FixedArrayTable.read_ofFn]
  rfl

theorem emit_cost {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable m ℝ) : (emit routes sampled).cost ≤ 8 * n + 2 := by
  have h := arrayRun_bound n 6 (routedCell routes sampled) (routedCell_cost routes sampled)
  simpa [emit, Nat.add_comm, Nat.mul_comm] using h

theorem emit_fullBudget {n m : ℕ} {G : ProportionalGroups n m}
    (p : RealPreparedGroupOutput G) (sampled : FixedArrayTable m ℝ) (B : ℝ)
    (hBudget : FullBudget B sampled.read) :
    FullBudget B (emit p.table sampled).value.read := by
  rw [emit_value]
  exact p.emit_fullBudget hBudget

noncomputable def routedMixedCell {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable (m + 1) ℝ) (j : Fin n) : Run ℝ :=
  let route := routes.read j
  match route.1 with
  | none => ⟨0, [.control, .control, .control, .load 0 0]⟩
  | some g =>
      let coefficient : Run ℝ := ⟨route.2, [.load j.val route.2]⟩
      let value := loadReal sampled g.castSucc
      let result := arithmetic .mul coefficient.value value.value
      ⟨result.value, [.control, .control, .control] ++ coefficient.trace ++ value.trace ++ result.trace⟩

theorem routedMixedCell_value {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable (m + 1) ℝ) (j : Fin n) :
    (routedMixedCell routes sampled j).value =
      match (routes.read j).1 with
      | none => 0
      | some g => (routes.read j).2 * sampled.read g.castSucc := by
  cases h : (routes.read j).1 <;> simp [routedMixedCell, h, loadReal, arithmetic,
    Operation.realValue, RealArithmeticOp.apply]

theorem routedMixedCell_cost {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable (m + 1) ℝ) (j : Fin n) :
    (routedMixedCell routes sampled j).cost ≤ 6 := by
  cases h : (routes.read j).1 <;> simp [routedMixedCell, h, Run.cost, loadReal, arithmetic, Operation.cost]

noncomputable def mixedCell {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable (m + 1) ℝ) (pivot : Fin n) (j : Fin n) : Run ℝ :=
  let base := routedMixedCell routes sampled j
  let extra : Run ℝ := if j = pivot then loadReal sampled (Fin.last m)
    else ⟨0, [.load 0 0]⟩
  let total := arithmetic .add base.value extra.value
  ⟨total.value, base.trace ++ [.control, .control] ++ extra.trace ++ total.trace⟩

theorem mixedCell_value {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable (m + 1) ℝ) (pivot : Fin n) (j : Fin n) :
    (mixedCell routes sampled pivot j).value =
      (match (routes.read j).1 with
      | none => 0
      | some g => (routes.read j).2 * sampled.read g.castSucc) +
        if j = pivot then sampled.read (Fin.last m) else 0 := by
  by_cases h : j = pivot <;> simp [mixedCell, routedMixedCell_value, h, loadReal,
    arithmetic, Operation.realValue, RealArithmeticOp.apply]

theorem mixedCell_cost {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable (m + 1) ℝ) (pivot : Fin n) (j : Fin n) :
    (mixedCell routes sampled pivot j).cost ≤ 10 := by
  have hb := routedMixedCell_cost routes sampled j
  unfold mixedCell Run.cost
  simp only [List.map_append, List.sum_append]
  change (routedMixedCell routes sampled j).cost + 2 +
    (if j = pivot then loadReal sampled (Fin.last m) else ⟨0, [.load 0 0]⟩ : Run ℝ).cost + 1 ≤ _
  unfold Run.cost at hb
  split <;> simp only [loadReal, Run.cost, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Operation.cost, Nat.add_zero] <;> omega

noncomputable def emitMixed {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable (m + 1) ℝ) (pivot : Fin n) : Run (FixedArrayTable n ℝ) :=
  arrayRun n (mixedCell routes sampled pivot)

theorem emitMixed_value {n m : ℕ} {G : ProportionalGroups n m}
    (p : RealPreparedGroupOutput G) (sampled : FixedArrayTable (m + 1) ℝ) (pivot : Fin n) :
    (emitMixed p.table sampled pivot).value = p.emitMixed pivot sampled.read := by
  apply table_ext
  intro j
  simp only [emitMixed, arrayRun_read, mixedCell_value, RealPreparedGroupOutput.emitMixed,
    FixedArrayTable.read_ofFn]
  rfl

theorem emitMixed_cost {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable (m + 1) ℝ) (pivot : Fin n) :
    (emitMixed routes sampled pivot).cost ≤ 12 * n + 2 := by
  have h := arrayRun_bound n 10 (mixedCell routes sampled pivot)
    (mixedCell_cost routes sampled pivot)
  simpa [emitMixed, Nat.add_comm, Nat.mul_comm] using h

theorem emitMixed_fullBudget {n m : ℕ} {G : ProportionalGroups n m}
    (p : RealPreparedGroupOutput G) (sampled : FixedArrayTable (m + 1) ℝ)
    (pivot : Fin n) (B : ℝ) (hBudget : FullBudget B sampled.read) :
    FullBudget B (emitMixed p.table sampled pivot).value.read := by
  rw [emitMixed_value]
  exact p.emitMixed_fullBudget pivot hBudget

/-- The reached final coordinate address comes from the retained array header.
The mathematical dimension appears only in the readback certificate. -/
noncomputable def cachedLastRead {m : ℕ} (sampled : FixedArrayTable (m + 1) ℝ) : Run ℝ :=
  let address : Fin (m + 1) := ⟨sampled.data.size - 1, by rw [sampled.size]; omega⟩
  let read := loadReal sampled address
  ⟨read.value, [.control, .control] ++ read.trace⟩

theorem cachedLastRead_value {m : ℕ} (sampled : FixedArrayTable (m + 1) ℝ) :
    (cachedLastRead sampled).value = sampled.read (Fin.last m) := by
  have h : (⟨sampled.data.size - 1, by rw [sampled.size]; omega⟩ : Fin (m + 1)) = Fin.last m := by
    apply Fin.ext
    simp [sampled.size]
  simp only [cachedLastRead, loadReal, Operation.realValue, h]

theorem cachedLastRead_cost {m : ℕ} (sampled : FixedArrayTable (m + 1) ℝ) :
    (cachedLastRead sampled).cost = 3 := rfl

noncomputable def cachedMixedCell {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable (m + 1) ℝ) (pivot : Fin n) (j : Fin n) : Run ℝ :=
  let base := routedMixedCell routes sampled j
  let extra : Run ℝ := if j = pivot then cachedLastRead sampled else ⟨0, [.load 0 0]⟩
  let total := arithmetic .add base.value extra.value
  ⟨total.value, base.trace ++ [.control, .control] ++ extra.trace ++ total.trace⟩

theorem cachedMixedCell_value {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable (m + 1) ℝ) (pivot : Fin n) (j : Fin n) :
    (cachedMixedCell routes sampled pivot j).value = (mixedCell routes sampled pivot j).value := by
  by_cases h : j = pivot <;> simp [cachedMixedCell, mixedCell, h, cachedLastRead_value,
    loadReal, arithmetic, Operation.realValue, RealArithmeticOp.apply]

theorem cachedMixedCell_cost {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable (m + 1) ℝ) (pivot : Fin n) (j : Fin n) :
    (cachedMixedCell routes sampled pivot j).cost ≤ 12 := by
  have hb := routedMixedCell_cost routes sampled j
  unfold cachedMixedCell Run.cost
  simp only [List.map_append, List.sum_append]
  change (routedMixedCell routes sampled j).cost + 2 +
    (if j = pivot then cachedLastRead sampled else ⟨0, [.load 0 0]⟩ : Run ℝ).cost + 1 ≤ _
  by_cases h : j = pivot
  · rw [if_pos h, cachedLastRead_cost]
    omega
  · rw [if_neg h]
    change (routedMixedCell routes sampled j).cost + 2 + 1 + 1 ≤ _
    omega

noncomputable def emitMixedCached {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable (m + 1) ℝ) (pivot : Fin n) : Run (FixedArrayTable n ℝ) :=
  arrayRun n (cachedMixedCell routes sampled pivot)

theorem emitMixedCached_value {n m : ℕ} {G : ProportionalGroups n m}
    (p : RealPreparedGroupOutput G) (sampled : FixedArrayTable (m + 1) ℝ) (pivot : Fin n) :
    (emitMixedCached p.table sampled pivot).value = p.emitMixed pivot sampled.read := by
  have h : (emitMixedCached p.table sampled pivot).value = (emitMixed p.table sampled pivot).value := by
    apply table_ext
    intro j
    simp only [emitMixedCached, emitMixed, arrayRun_read, cachedMixedCell_value]
  exact h.trans (emitMixed_value p sampled pivot)

theorem emitMixedCached_cost {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable (m + 1) ℝ) (pivot : Fin n) :
    (emitMixedCached routes sampled pivot).cost ≤ 14 * n + 2 := by
  have h := arrayRun_bound n 12 (cachedMixedCell routes sampled pivot)
    (cachedMixedCell_cost routes sampled pivot)
  simpa [emitMixedCached, Nat.add_comm, Nat.mul_comm] using h

theorem emitMixedCached_fullBudget {n m : ℕ} {G : ProportionalGroups n m}
    (p : RealPreparedGroupOutput G) (sampled : FixedArrayTable (m + 1) ℝ)
    (pivot : Fin n) (B : ℝ) (hBudget : FullBudget B sampled.read) :
    FullBudget B (emitMixedCached p.table sampled pivot).value.read := by
  rw [emitMixedCached_value]
  exact p.emitMixed_fullBudget pivot hBudget

noncomputable def scale {n : ℕ} (factor : ℝ) (row : FixedArrayTable n ℝ) :
    Run (FixedArrayTable n ℝ) :=
  arrayRun n (fun j =>
    let available : Run ℝ := ⟨factor, [.load 0 factor]⟩
    let coordinate := loadReal row j
    let result := arithmetic .mul available.value coordinate.value
    ⟨result.value, available.trace ++ coordinate.trace ++ result.trace⟩)

theorem scale_value {n : ℕ} (factor : ℝ) (row : FixedArrayTable n ℝ) (j : Fin n) :
    (scale factor row).value.read j = factor * row.read j := by
  simp [scale, arrayRun_read, loadReal, arithmetic, Operation.realValue, RealArithmeticOp.apply]

theorem scale_cost {n : ℕ} (factor : ℝ) (row : FixedArrayTable n ℝ) :
    (scale factor row).cost = 5 * n + 2 := by
  unfold scale
  rw [arrayRun_cost]
  simp [Run.cost, loadReal, arithmetic, Operation.cost, Nat.mul_comm]
  omega

theorem scale_fullBudget {n : ℕ} (factor : ℝ) (row : FixedArrayTable n ℝ)
    (B : ℝ) (hFactor : 0 ≤ factor) (hBudget : FullBudget B row.read) :
    FullBudget (factor * B) (scale factor row).value.read := by
  constructor
  · intro j
    rw [scale_value]
    exact mul_nonneg hFactor (hBudget.1 j)
  · simp_rw [scale_value]
    rw [← Finset.mul_sum, hBudget.2]

noncomputable def emitScale {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable m ℝ) (factor : ℝ) : Run (FixedArrayTable n ℝ) :=
  let emitted := emit routes sampled
  let scaled := scale factor emitted.value
  ⟨scaled.value, emitted.trace ++ scaled.trace⟩

theorem emitScale_cost {n m : ℕ} (routes : FixedArrayTable n (RealGroupRoute m))
    (sampled : FixedArrayTable m ℝ) (factor : ℝ) :
    (emitScale routes sampled factor).cost ≤ 13 * n + 4 := by
  change cost ((emit routes sampled).trace ++ (scale factor (emit routes sampled).value).trace) ≤ _
  rw [cost_append]
  change (emit routes sampled).cost + (scale factor (emit routes sampled).value).cost ≤ _
  rw [scale_cost]
  have h := emit_cost routes sampled
  omega

theorem emitScale_fullBudget {n m : ℕ} {G : ProportionalGroups n m}
    (p : RealPreparedGroupOutput G) (sampled : FixedArrayTable m ℝ)
    (factor B : ℝ) (hFactor : 0 ≤ factor) (hBudget : FullBudget B sampled.read) :
    FullBudget (factor * B) (emitScale p.table sampled factor).value.read :=
  scale_fullBudget factor _ B hFactor (emit_fullBudget p sampled B hBudget)

end Blotto.RealPRGPackingExecution
