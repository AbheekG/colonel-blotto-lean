import Blotto.PureBoundaryEquilibria
import Blotto.RealPRGGlobalExecution
import Blotto.ProductFiniteTraining

/-! Complete equal-budget selection from stored original real input cells.
An actual header-driven scan selects a field of value at least one half. That
branch produces a full-budget vertex array. If the scan fails, its checked
result supplies the PRG small-field proof, and an actual verified original
PRG cache is prepared from the same stored values and available budget.
Every draw produces a whole stored allocation; independent seeds give the
independent product of its two exact Nash laws. Named exact-real arithmetic,
comparison, uniform and word/cell/control operations have linear derived
costs. Rational input parsing, finite-binary execution, lifetime and host
allocator costs are separate. No general unequal-budget selector is claimed. -/

namespace Blotto.RealEqualBudgetExecution
open MeasureTheory PRGRealRAMExecution PRGExactRealRAMContract RealPRGNativeFactoryExecution
open scoped BigOperators Classical

structure Input (n : ℕ) where
  values : RationalFieldSelector n
  budget : ℚ
  budget_pos : 0 < budget

noncomputable def Input.prg {n : ℕ} (i : Input n)
    (small : ∀ j, (i.values.weight j : ℝ) ≤ 1 / 2) : RationalPRGOriginalInput n where
  values := i.values.weight
  positive := i.values.positive
  normalized := i.values.sum_one
  a := i.budget
  b := i.budget
  a_pos := i.budget_pos
  b_pos := i.budget_pos
  b_le := le_rfl
  small_fields := by
    intro j
    have hReal : (i.values.weight j : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by
      simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using small j
    have h : i.values.weight j ≤ (1 / 2 : ℚ) := by exact_mod_cast hReal
    nlinarith [i.budget_pos]

theorem Input.prg_values {n : ℕ} (i : Input n)
    (small : ∀ j, (i.values.weight j : ℝ) ≤ 1 / 2) :
    (i.prg small).realValues = i.values.values := rfl

noncomputable def indices {n : ℕ} (values : FixedArrayTable n ℝ) : Run (List (Fin n)) :=
  let generated := RealPRGResourceExecution.addressRange values.data.size
  ⟨values.size ▸ generated.value,generated.trace ++ [.control]⟩

theorem indices_value {n : ℕ} (values : FixedArrayTable n ℝ) :
    (indices values).value = List.finRange n := by
  cases values with
  | mk data size =>
    cases size
    exact RealPRGResourceExecution.addressRange_value data.size

theorem indices_cost {n : ℕ} (values : FixedArrayTable n ℝ) :
    (indices values).cost ≤ 5 * n + 4 := by
  have h := RealPRGResourceExecution.addressRange_cost values.data.size
  unfold indices
  change cost (_ ++ _) ≤ _
  rw [cost_append]
  change (RealPRGResourceExecution.addressRange values.data.size).cost + 1 ≤ _
  have hSize := values.size
  omega

noncomputable def findHeavy {n : ℕ} (values : FixedArrayTable n ℝ) (half : ℝ) :
    List (Fin n) → Run (Option (Fin n))
  | [] => ⟨none,[.control]⟩
  | j :: rest =>
      let loaded := loadReal values j
      let tested := compareLe half loaded.value
      join loaded (join tested (if tested.value then ⟨some j,[.storeCell 0,.control,.control]⟩
        else join (⟨(),[.control]⟩ : Run Unit) (findHeavy values half rest)))

theorem findHeavy_value {n : ℕ} (values : FixedArrayTable n ℝ) (half : ℝ) (items : List (Fin n)) :
    (findHeavy values half items).value = items.find? (fun j => decide (half ≤ values.read j)) := by
  induction items with
  | nil => rfl
  | cons j rest ih =>
    unfold findHeavy
    simp only [join_value]
    split
    · rename_i h
      have hp : decide (half ≤ values.read j) = true := h
      simp only [List.find?_cons,hp]
    · rename_i h
      have hp : ¬decide (half ≤ values.read j) = true := h
      simp only [List.find?_cons,hp,join_value,ih]

theorem findHeavy_cost {n : ℕ} (values : FixedArrayTable n ℝ) (half : ℝ) (items : List (Fin n)) :
    (findHeavy values half items).cost ≤ 5 * items.length + 1 := by
  induction items with
  | nil => exact le_rfl
  | cons j rest ih =>
    unfold findHeavy
    rw [join_cost,join_cost]
    change 1 + (1 + _) ≤ _
    split
    · change 1 + (1 + 3) ≤ _
      simp only [List.length_cons]
      omega
    · rw [join_cost]
      change 1 + (1 + (1 + _)) ≤ _
      simp only [List.length_cons]
      omega

theorem findHeavy_some {n : ℕ} (values : FixedArrayTable n ℝ) (half : ℝ) (items : List (Fin n))
    (j : Fin n) (h : (findHeavy values half items).value = some j) : half ≤ values.read j := by
  rw [findHeavy_value] at h
  exact of_decide_eq_true (List.find?_some (p := fun k => decide (half ≤ values.read k)) h)

theorem findHeavy_none {n : ℕ} (values : FixedArrayTable n ℝ) (half : ℝ)
    (h : (findHeavy values half (indices values).value).value = none) :
    ∀ j, values.read j < half := by
  rw [findHeavy_value,indices_value] at h
  simp only [List.find?_eq_none,List.mem_finRange,forall_const,decide_eq_true_eq,not_le] at h
  exact h

noncomputable def vertexArray {n : ℕ} (values : FixedArrayTable n ℝ) (budget : ℝ) (chosen : Fin n) :
    Run (FixedArrayTable n ℝ) :=
  let emitted := arrayRun values.data.size (fun j =>
    let value := if j.val = chosen.val then budget else 0
    (⟨value,[.control,.load 0 value,.control]⟩ : Run ℝ))
  ⟨⟨emitted.value.data,emitted.value.size.trans values.size⟩,emitted.trace⟩

theorem vertexArray_value {n : ℕ} (values : FixedArrayTable n ℝ) (budget : ℝ) (chosen : Fin n) :
    (vertexArray values budget chosen).value.read = PureBoundaryEquilibria.vertex budget chosen := by
  cases values with
  | mk data size =>
    cases size
    funext j
    rw [show (vertexArray ⟨data,rfl⟩ budget chosen).value.read j =
      (arrayRun data.size (fun k => (⟨if k.val = chosen.val then budget else 0,
        [.control,.load 0 (if k.val = chosen.val then budget else 0),.control]⟩ : Run ℝ))).value.read j from rfl,
      arrayRun_read]
    simp only [PureBoundaryEquilibria.vertex,Fin.ext_iff]

theorem vertexArray_cost {n : ℕ} (values : FixedArrayTable n ℝ) (budget : ℝ) (chosen : Fin n) :
    (vertexArray values budget chosen).cost ≤ 5 * n + 2 := by
  have h := arrayRun_bound values.data.size 3 (fun j =>
    (⟨if j.val = chosen.val then budget else 0,
      [.control,.load 0 (if j.val = chosen.val then budget else 0),.control]⟩ : Run ℝ)) (fun _ => by rfl)
  change (arrayRun values.data.size _).cost ≤ _
  have hb : 2 + values.data.size * (3 + 2) ≤ 5 * n + 2 := by rw [values.size]; omega
  exact h.trans hb

inductive Prepared {n : ℕ} (i : Input n) where
  | dominant (chosen : Fin n) (row : FixedArrayTable n ℝ)
      (hRow : row.read = PureBoundaryEquilibria.vertex (i.budget : ℝ) chosen)
      (hHeavy : 1 / 2 ≤ i.values.values.weight chosen)
  | coupled (small : ∀ j, (i.values.weight j : ℝ) ≤ 1 / 2)
      (cache : RealPRGInputExecution.Prepared (i.prg small))

noncomputable def prepare {n : ℕ} (i : Input n) (values : FixedArrayTable n ℝ)
    (hV : values.read = i.values.values.weight) (availableBudget : ℝ) (hB : availableBudget = (i.budget : ℝ)) :
    Run (Prepared i) := by
  let budget := RealPRGInputExecution.scalar 0 availableBudget
  let one := RealPRGInputExecution.scalar 1 1
  let two := RealPRGInputExecution.scalar 2 2
  let half := arithmetic .div one.value two.value
  let addresses := indices values
  let selected := findHeavy values half.value addresses.value
  match hs : selected.value with
  | some chosen =>
    let row := vertexArray values budget.value chosen
    have hHeavy : 1 / 2 ≤ i.values.values.weight chosen := by
      have h := findHeavy_some values half.value addresses.value chosen hs
      change 1 / 2 ≤ values.read chosen at h
      rw [hV] at h
      exact h
    have hRow : row.value.read = PureBoundaryEquilibria.vertex (i.budget : ℝ) chosen := by
      rw [vertexArray_value]
      exact congrArg (fun B => PureBoundaryEquilibria.vertex B chosen) hB
    exact join budget (join one (join two (join half (join addresses (join selected
      (join row ⟨.dominant chosen row.value hRow hHeavy,[.storeCell 0,.storeCell 1,.control]⟩))))))
  | none =>
    have small : ∀ j, (i.values.weight j : ℝ) ≤ 1 / 2 := by
      intro j
      have h := findHeavy_none values half.value hs j
      change values.read j < 1 / 2 at h
      rw [hV] at h
      exact h.le
    let tested := RealPRGInputExecution.recognize values budget.value budget.value
    let cache := RealPRGInputExecution.prepare (i.prg small) values hV budget.value budget.value hB hB
    exact join budget (join one (join two (join half (join addresses (join selected
      (join tested (join cache ⟨.coupled small cache.value,[.storeCell 0,.control,.control]⟩)))))))

theorem prepare_cost {n : ℕ} (i : Input n) (values : FixedArrayTable n ℝ)
    (hV : values.read = i.values.values.weight) (availableBudget : ℝ) (hB : availableBudget = (i.budget : ℝ)) :
    (prepare i values hV availableBudget hB).cost ≤ 40 * n + 120 := by
  have hi := indices_cost values
  have hs := findHeavy_cost values (arithmetic .div
    (RealPRGInputExecution.scalar 1 1).value (RealPRGInputExecution.scalar 2 2).value).value (indices values).value
  have hLength : (indices values).value.length = n := by rw [indices_value,List.length_finRange]
  rw [hLength] at hs
  unfold prepare
  dsimp only
  split
  · rename_i chosen hChosen
    have hv := vertexArray_cost values (RealPRGInputExecution.scalar 0 availableBudget).value chosen
    rw [join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost]
    change 1 + (1 + (1 + (1 + (_ + (_ + (_ + 3)))))) ≤ _
    omega
  · rename_i hNone
    have hr := RealPRGInputExecution.recognize_cost values availableBudget availableBudget
    have hp := RealPRGInputExecution.prepare_cost
      (i.prg (fun j => (by
        have h := findHeavy_none values (arithmetic .div
          (RealPRGInputExecution.scalar 1 1).value (RealPRGInputExecution.scalar 2 2).value).value hNone j
        change values.read j < 1 / 2 at h
        rw [hV] at h
        exact h.le))) values hV availableBudget availableBudget hB hB
    rw [join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost]
    change 1 + (1 + (1 + (1 + (_ + (_ + (_ + (_ + 3))))))) ≤ _
    have hSize := values.size
    dsimp only [RealPRGInputExecution.scalar] at *
    omega

noncomputable def draw {n : ℕ} {i : Input n} (prepared : Prepared i) (player : Bool) (seed : RealLottoSeed n) :
    Run (FixedArrayTable n ℝ) :=
  match prepared with
  | .dominant _ row _ _ => join (⟨(),[.control]⟩ : Run Unit) (RealPRGResourceExecution.copyStored row)
  | .coupled _ cache => join (⟨(),[.control]⟩ : Run Unit) (RealPRGGlobalExecution.cachedDraw cache player seed)

noncomputable def law {n : ℕ} {i : Input n} (prepared : Prepared i) (player : Bool) : Mixed n :=
  match prepared with
  | .dominant _ row _ _ => PureBoundaryEquilibria.pointLaw row.read
  | .coupled _ cache => RealPRGGlobalExecution.cachedLaw cache player

theorem draw_cost {n : ℕ} {i : Input n} (prepared : Prepared i) (player : Bool) (seed : RealLottoSeed n) :
    (draw prepared player seed).cost ≤ 245 * n + 428191 := by
  cases prepared with
  | dominant chosen row hRow hHeavy =>
    rw [draw,join_cost]
    have h := RealPRGResourceExecution.copyStored_cost row
    change 1 + _ ≤ _
    omega
  | coupled small cache =>
    rw [draw,join_cost]
    have h := RealPRGGlobalExecution.cachedDraw_cost cache player seed
    change 1 + _ ≤ _
    omega

theorem draw_fullBudget {n : ℕ} {i : Input n} (prepared : Prepared i) (player : Bool) (seed : RealLottoSeed n)
    (hs : realGroupSeedValid seed.2) : FullBudget (i.budget : ℝ) (draw prepared player seed).value.read := by
  have hB : (0 : ℝ) ≤ i.budget := by exact_mod_cast i.budget_pos.le
  cases prepared with
  | dominant chosen row hRow hHeavy =>
    simp only [draw,join_value,RealPRGResourceExecution.copyStored_value,hRow]
    exact PureBoundaryEquilibria.vertex_fullBudget _ hB chosen
  | coupled small cache =>
    have h := RealPRGGlobalExecution.cachedDraw_fullBudget cache player seed hs
    change FullBudget (if player then (i.budget : ℝ) else (i.budget : ℝ)) _ at h
    simpa only [ite_self,draw,join_value] using h

theorem draw_feasible {n : ℕ} {i : Input n} (prepared : Prepared i) (player : Bool) (seed : RealLottoSeed n)
    (hs : realGroupSeedValid seed.2) : Feasible (i.budget : ℝ) (draw prepared player seed).value.read :=
  fullBudget_feasible (draw_fullBudget prepared player seed hs)

theorem draw_law {n : ℕ} {i : Input n} (prepared : Prepared i) (player : Bool) :
    Measure.map (fun seed => (draw prepared player seed).value.read)
      (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)) =
        (law prepared player : Measure (Allocation n)) := by
  cases prepared with
  | dominant chosen row hRow hHeavy =>
    simp only [draw,join_value,RealPRGResourceExecution.copyStored_value]
    rw [Measure.map_const,measure_univ,one_smul]
    rfl
  | coupled small cache => rfl

theorem draw_measurable {n : ℕ} {i : Input n} (prepared : Prepared i) (player : Bool) :
    Measurable (fun seed => (draw prepared player seed).value.read) := by
  cases prepared with
  | dominant chosen row hRow hHeavy =>
    simp only [draw,join_value,RealPRGResourceExecution.copyStored_value]
    exact measurable_const
  | coupled small cache => exact RealPRGGlobalExecution.cachedDraw_measurable cache player

theorem draw_product_law {n : ℕ} {i : Input n} (prepared : Prepared i) :
    Measure.map (Prod.map (fun seed => (draw prepared true seed).value.read)
      (fun seed => (draw prepared false seed).value.read))
      ((LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)).prod
        (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n))) =
      (law prepared true : Measure (Allocation n)).prod (law prepared false : Measure (Allocation n)) := by
  rw [← Measure.map_prod_map _ _ (draw_measurable prepared true) (draw_measurable prepared false),draw_law,draw_law]

theorem law_supported {n : ℕ} {i : Input n} (prepared : Prepared i) (player : Bool) :
    Supported (i.budget : ℝ) (law prepared player) := by
  have hB : (0 : ℝ) ≤ i.budget := by exact_mod_cast i.budget_pos.le
  cases prepared with
  | dominant chosen row hRow hHeavy =>
    simp only [law,hRow]
    exact PureBoundaryEquilibria.pointLaw_supported _ _
      (fullBudget_feasible (PureBoundaryEquilibria.vertex_fullBudget _ hB chosen))
  | coupled small cache =>
    rw [law,RealPRGGlobalExecution.cachedLaw_state]
    cases player
    · change Supported (i.budget : ℝ) (i.prg small).realPoorLaw
      have hBase : Supported ((i.prg small).normalizedInput.b : ℝ)
          (i.prg small).normalizedInput.real.realPoorLaw := by
        rw [PRGInput.realPoorLaw_eq]
        exact (i.prg small).normalizedInput.real.poorSystem.law_supported
      have h := scaleLaw_supported hB _ hBase
      change Supported (((i.prg small).a : ℝ) * ((i.prg small).normalizedInput.b : ℝ)) (i.prg small).realPoorLaw at h
      rw [(i.prg small).rescaled_poor_budget] at h
      exact h
    · change Supported (i.budget : ℝ) (i.prg small).realRichLaw
      have hBase : Supported 1 (i.prg small).normalizedInput.real.realRichLaw := by
        rw [PRGInput.realRichLaw_eq]
        exact (i.prg small).normalizedInput.real.richSystem.law_supported
      change Supported (i.budget : ℝ) (scaleLaw (i.budget : ℝ) (i.prg small).normalizedInput.real.realRichLaw)
      simpa only [mul_one] using scaleLaw_supported hB _ hBase

theorem equilibrium {n : ℕ} {i : Input n} (prepared : Prepared i) :
    regret i.values.values (i.budget : ℝ) (law prepared true) (law prepared false) = 0 ∧
      regret i.values.values (i.budget : ℝ) (law prepared false) (law prepared true) = 0 := by
  cases prepared with
  | dominant chosen row hRow hHeavy =>
    have hB : (0 : ℝ) ≤ i.budget := by exact_mod_cast i.budget_pos.le
    simp only [law,hRow]
    have h := (PureBoundaryEquilibria.dominant_vertex_equilibrium i.values.values _ hB chosen hHeavy).2
    exact ⟨h,h⟩
  | coupled small cache =>
    have h := RealPRGGlobalExecution.cachedDraw_equilibrium cache
    change regret i.values.values (i.budget : ℝ) (law (.coupled small cache) true) (law (.coupled small cache) false) = 0 ∧
      regret i.values.values (i.budget : ℝ) (law (.coupled small cache) false) (law (.coupled small cache) true) = 0 ∧ _ at h
    exact ⟨h.1,h.2.1⟩

noncomputable def run {n : ℕ} (i : Input n) (values : FixedArrayTable n ℝ)
    (hV : values.read = i.values.values.weight) (availableBudget : ℝ) (hB : availableBudget = (i.budget : ℝ))
    (player : Bool) (seed : RealLottoSeed n) : Run (FixedArrayTable n ℝ) :=
  let prepared := prepare i values hV availableBudget hB
  join prepared (draw prepared.value player seed)

theorem run_cost {n : ℕ} (i : Input n) (values : FixedArrayTable n ℝ)
    (hV : values.read = i.values.values.weight) (availableBudget : ℝ) (hB : availableBudget = (i.budget : ℝ))
    (player : Bool) (seed : RealLottoSeed n) :
    (run i values hV availableBudget hB player seed).cost ≤ 285 * values.data.size + 428311 := by
  have hp := prepare_cost i values hV availableBudget hB
  have hd := draw_cost (prepare i values hV availableBudget hB).value player seed
  rw [run,join_cost]
  have hSize := values.size
  omega

theorem run_fullBudget {n : ℕ} (i : Input n) (values : FixedArrayTable n ℝ)
    (hV : values.read = i.values.values.weight) (availableBudget : ℝ) (hB : availableBudget = (i.budget : ℝ))
    (player : Bool) (seed : RealLottoSeed n) (hs : realGroupSeedValid seed.2) :
    FullBudget (i.budget : ℝ) (run i values hV availableBudget hB player seed).value.read :=
  draw_fullBudget _ _ _ hs

theorem run_feasible {n : ℕ} (i : Input n) (values : FixedArrayTable n ℝ)
    (hV : values.read = i.values.values.weight) (availableBudget : ℝ) (hB : availableBudget = (i.budget : ℝ))
    (player : Bool) (seed : RealLottoSeed n) (hs : realGroupSeedValid seed.2) :
    Feasible (i.budget : ℝ) (run i values hV availableBudget hB player seed).value.read :=
  fullBudget_feasible (run_fullBudget i values hV availableBudget hB player seed hs)

noncomputable def outputLaw {n : ℕ} (i : Input n) (values : FixedArrayTable n ℝ)
    (hV : values.read = i.values.values.weight) (availableBudget : ℝ) (hB : availableBudget = (i.budget : ℝ))
    (player : Bool) : Mixed n := law (prepare i values hV availableBudget hB).value player

theorem run_law {n : ℕ} (i : Input n) (values : FixedArrayTable n ℝ)
    (hV : values.read = i.values.values.weight) (availableBudget : ℝ) (hB : availableBudget = (i.budget : ℝ))
    (player : Bool) :
    Measure.map (fun seed => (run i values hV availableBudget hB player seed).value.read)
      (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)) =
        (outputLaw i values hV availableBudget hB player : Measure (Allocation n)) :=
  draw_law _ _

theorem run_product_law {n : ℕ} (i : Input n) (values : FixedArrayTable n ℝ)
    (hV : values.read = i.values.values.weight) (availableBudget : ℝ) (hB : availableBudget = (i.budget : ℝ)) :
    Measure.map (Prod.map (fun seed => (run i values hV availableBudget hB true seed).value.read)
      (fun seed => (run i values hV availableBudget hB false seed).value.read))
      ((LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n)).prod
        (LottoResourceSystem.realInputLaw n : Measure (RealLottoSeed n))) =
      (outputLaw i values hV availableBudget hB true : Measure (Allocation n)).prod
        (outputLaw i values hV availableBudget hB false : Measure (Allocation n)) :=
  draw_product_law _

theorem output_equilibrium {n : ℕ} (i : Input n) (values : FixedArrayTable n ℝ)
    (hV : values.read = i.values.values.weight) (availableBudget : ℝ) (hB : availableBudget = (i.budget : ℝ)) :
    Supported (i.budget : ℝ) (outputLaw i values hV availableBudget hB true) ∧
      Supported (i.budget : ℝ) (outputLaw i values hV availableBudget hB false) ∧
      regret i.values.values (i.budget : ℝ) (outputLaw i values hV availableBudget hB true)
        (outputLaw i values hV availableBudget hB false) = 0 ∧
      regret i.values.values (i.budget : ℝ) (outputLaw i values hV availableBudget hB false)
        (outputLaw i values hV availableBudget hB true) = 0 :=
  ⟨law_supported _ true,law_supported _ false,equilibrium _⟩

end Blotto.RealEqualBudgetExecution
