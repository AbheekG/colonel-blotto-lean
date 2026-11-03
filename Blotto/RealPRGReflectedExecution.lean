import Blotto.RealPRGFourNativeExecution

/-! Complete named-operation execution of the fixed-size reflected and
four-variable factories. The three-resource source visits only the selected
path, constructs its reached nested terminal, and emits the original row.
The small branch, gluing branch, three-comparison sort and inverse restoration
retain the previous complete exact-real sampler on every input packet.

Costs refer to the explicit PRGRealRAMExecution primitive model, with stored
input reals and unit-cost independent exact uniforms. They include the native
parameter, comparison, control, array, and selected arithmetic stages below;
they are neither Lean-host nor bit-backend costs. Whole global resource,
packing, original-input and output composition remain separate obligations. -/
namespace Blotto.RealPRGReflectedExecution
open MeasureTheory PRGRealRAMExecution PRGExactRealRAMContract RealPRGNativeFactoryExecution RealPRGFourNativeExecution
open scoped BigOperators Classical

noncomputable def fractionalProbe (cap resource : FixedArrayTable 3 ℝ) (j : Fin 3) : Run Bool :=
  let l := loadReal cap j
  let r := loadReal resource j
  let lower := compareLt 0 r.value
  let upper := compareLt r.value l.value
  join l (join r (join lower (join upper ⟨lower.value && upper.value,[.control]⟩)))

theorem fractionalProbe_value (cap resource : FixedArrayTable 3 ℝ) (j : Fin 3) :
    (fractionalProbe cap resource j).value = decide (Fractional cap.read resource.read j) := by
  by_cases hL : 0 < resource.read j <;> by_cases hU : resource.read j < cap.read j <;>
    simp [fractionalProbe,join_value,loadReal,Operation.realValue,compareLt,Fractional,hL,hU]

theorem fractionalProbe_cost (cap resource : FixedArrayTable 3 ℝ) (j : Fin 3) :
    (fractionalProbe cap resource j).cost ≤ 5 := by
  unfold fractionalProbe
  rw [join_cost,join_cost,join_cost,join_cost]
  change 1 + (1 + (1 + (1 + 1))) ≤ 5
  decide

noncomputable def selectedPair (cap resource : FixedArrayTable 3 ℝ) : Run (Option (Fin 3 × Fin 3)) :=
  let flags := arrayRun 3 (fractionalProbe cap resource)
  let result := if flags.value.read 0 && flags.value.read 1 then some (0,1) else
    if flags.value.read 0 && flags.value.read 2 then some (0,2) else
      if flags.value.read 1 && flags.value.read 2 then some (1,2) else none
  join flags ⟨result,[.control,.control,.control,.control,.control,.control]⟩

theorem selectedPair_value (cap resource : FixedArrayTable 3 ℝ) :
    (selectedPair cap resource).value =
      if Fractional cap.read resource.read 0 ∧ Fractional cap.read resource.read 1 then some (0,1) else
        if Fractional cap.read resource.read 0 ∧ Fractional cap.read resource.read 2 then some (0,2) else
          if Fractional cap.read resource.read 1 ∧ Fractional cap.read resource.read 2 then some (1,2) else none := by
  simp [selectedPair,join_value,arrayRun_read,fractionalProbe_value]

theorem selectedPair_cost (cap resource : FixedArrayTable 3 ℝ) : (selectedPair cap resource).cost ≤ 30 := by
  have hf := arrayRun_bound 3 5 (fractionalProbe cap resource) (fractionalProbe_cost cap resource)
  unfold selectedPair
  rw [join_cost]
  change _ + 6 ≤ 30
  omega

theorem selectedPair_complete (cap resource : FixedArrayTable 3 ℝ) :
    (selectedPair cap resource).value =
      if h : 1 < (fractionalSet cap.read resource.read).card then
        some ((selectThreePair cap.read resource.read h).i,(selectThreePair cap.read resource.read h).j) else none := by
  rw [selectedPair_value]
  by_cases h : 1 < (fractionalSet cap.read resource.read).card
  · simp only [dite_eq_left h]
    by_cases h01 : Fractional cap.read resource.read 0 ∧ Fractional cap.read resource.read 1
    · simp [selectThreePair,h01]
    · by_cases h02 : Fractional cap.read resource.read 0 ∧ Fractional cap.read resource.read 2
      · have hn1 : ¬ Fractional cap.read resource.read 1 := fun h1 => h01 ⟨h02.1,h1⟩
        simp [selectThreePair,h02,hn1]
      · have h12 : Fractional cap.read resource.read 1 ∧ Fractional cap.read resource.read 2 := by
          rcases Finset.one_lt_card.mp h with ⟨a,ha,b,hb,hab⟩
          fin_cases a <;> fin_cases b <;> simp_all [mem_fractionalSet]
        have hn0 : ¬ Fractional cap.read resource.read 0 := fun h0 => h01 ⟨h0,h12.1⟩
        simp [selectThreePair,hn0,h12]
  · simp only [dite_eq_right h]
    have hPair : ∀ a b : Fin 3, a ≠ b → ¬ (Fractional cap.read resource.read a ∧ Fractional cap.read resource.read b) := by
      intro a b hab hp
      apply h
      exact Finset.one_lt_card.mpr ⟨a,(mem_fractionalSet _ _ _).mpr hp.1,b,(mem_fractionalSet _ _ _).mpr hp.2,hab⟩
    simp [hPair 0 1 (by decide),hPair 0 2 (by decide),hPair 1 2 (by decide)]

structure PairValues where
  total : ℝ
  lower : ℝ
  upper : ℝ
  probability : ℝ

noncomputable def pairValues (cap resource : FixedArrayTable 3 ℝ) (i j : Fin 3) : Run PairValues :=
  let li := loadReal cap i
  let lj := loadReal cap j
  let ri := loadReal resource i
  let rj := loadReal resource j
  let total := arithmetic .add ri.value rj.value
  let candidate := arithmetic .sub total.value lj.value
  let lower := arithmetic .maximum 0 candidate.value
  let upper := arithmetic .minimum li.value total.value
  let numerator := arithmetic .sub ri.value lower.value
  let denominator := arithmetic .sub upper.value lower.value
  let probability := arithmetic .div numerator.value denominator.value
  join li <| join lj <| join ri <| join rj <| join total <| join candidate <| join lower <| join upper <|
    join numerator <| join denominator <| join probability <|
      ⟨⟨total.value,lower.value,upper.value,probability.value⟩,[.storeCell 0,.storeCell 1,.storeCell 2,.storeCell 3]⟩

theorem pairValues_value (cap resource : FixedArrayTable 3 ℝ) (i j : Fin 3)
    (hi : Fractional cap.read resource.read i) (hj : Fractional cap.read resource.read j) :
    let p := resourcePair cap.read resource.read i j hi hj
    (pairValues cap resource i j).value = ⟨p.total,p.lower,p.upper,p.probability⟩ := by
  simp [pairValues,join_value,loadReal,arithmetic,Operation.realValue,RealArithmeticOp.apply,
    resourcePair,RoundingPair.total,RoundingPair.lower,RoundingPair.upper,RoundingPair.probability]

theorem pairValues_cost (cap resource : FixedArrayTable 3 ℝ) (i j : Fin 3) : (pairValues cap resource i j).cost ≤ 20 := by
  unfold pairValues
  rw [join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost]
  change 1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (1 + 4)))))))))) ≤ 20
  decide

noncomputable def update (resource : FixedArrayTable 3 ℝ) (i j : Fin 3) (total first : ℝ) : Run (FixedArrayTable 3 ℝ) :=
  let second := arithmetic .sub total first
  let cells := arrayRun 3 (fun k =>
    if k = i then ⟨first,[.control,.store k.val first]⟩ else
      if k = j then ⟨second.value,[.control,.control,.store k.val second.value]⟩ else
        join (⟨(),[.control,.control]⟩ : Run Unit) (loadReal resource k))
  join second cells

theorem update_value (resource : FixedArrayTable 3 ℝ) (i j : Fin 3) (hij : i ≠ j) (first : ℝ) :
    (update resource i j (resource.read i + resource.read j) first).value.read = updatePair resource.read i j first := by
  funext k
  simp only [update,join_value,arrayRun_read,arithmetic,Operation.realValue,RealArithmeticOp.apply,updatePair]
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [hki]
    · simp [hki,hkj,join_value,loadReal,Operation.realValue]

theorem update_cost (resource : FixedArrayTable 3 ℝ) (i j : Fin 3) (total first : ℝ) :
    (update resource i j total first).cost ≤ 20 := by
  have hb : ∀ k : Fin 3,
      (if k = i then (⟨first,[Operation.control,.store k.val first]⟩ : Run ℝ) else
        if k = j then ⟨(arithmetic .sub total first).value,[.control,.control,.store k.val (arithmetic .sub total first).value]⟩ else
          join (⟨(),[.control,.control]⟩ : Run Unit) (loadReal resource k)).cost ≤ 3 := by
    intro k
    split_ifs
    · change 2 ≤ 3; decide
    · change 3 ≤ 3; decide
    · rw [join_cost]
      change 2 + 1 ≤ 3
      decide
  have hc := arrayRun_bound 3 3 _ hb
  unfold update
  rw [join_cost]
  change 1 + _ ≤ 20
  omega

noncomputable def resourceLoop (cap : FixedArrayTable 3 ℝ) :
    (C : ℕ) → FixedArrayTable 3 ℝ → (Fin C → ℝ) → Run (FixedArrayTable 3 ℝ)
  | 0, resource, _ => ⟨resource,[.control]⟩
  | C + 1, resource, seed =>
    let selected := selectedPair cap resource
    match selected.value with
    | none => join selected ⟨resource,[.control]⟩
    | some pair =>
      let fields := pairValues cap resource pair.1 pair.2
      let u := uniform (seed 0)
      let compared := compareLe u.value fields.value.probability
      let first := if compared.value then fields.value.upper else fields.value.lower
      let updated := update resource pair.1 pair.2 fields.value.total first
      join selected (join fields (join u (join compared (join updated
        (join (⟨(),[.control,.control]⟩ : Run Unit) (resourceLoop cap C updated.value (Fin.tail seed)))))))

theorem resourceLoop_cost (cap : FixedArrayTable 3 ℝ) (C : ℕ) (resource : FixedArrayTable 3 ℝ) (seed : Fin C → ℝ) :
    (resourceLoop cap C resource seed).cost ≤ 100 * C + 1 := by
  induction C generalizing resource with
  | zero => simp [resourceLoop,Run.cost,Operation.cost]
  | succ C ih =>
    have hs := selectedPair_cost cap resource
    unfold resourceLoop
    dsimp only
    split
    · rw [join_cost]
      change _ + 1 ≤ _
      omega
    · rename_i pair _hPair
      rw [join_cost,join_cost,join_cost,join_cost,join_cost,join_cost]
      have hp := pairValues_cost cap resource pair.1 pair.2
      have hu : (uniform (seed 0)).cost = 1 := rfl
      have hCompare : (compareLe (uniform (seed 0)).value (pairValues cap resource pair.1 pair.2).value.probability).cost = 1 := rfl
      have hControl : (⟨(),[Operation.control,.control]⟩ : Run Unit).cost = 2 := rfl
      have hx := update_cost resource pair.1 pair.2 (pairValues cap resource pair.1 pair.2).value.total
        (if (compareLe (uniform (seed 0)).value (pairValues cap resource pair.1 pair.2).value.probability).value then
          (pairValues cap resource pair.1 pair.2).value.upper else (pairValues cap resource pair.1 pair.2).value.lower)
      have hl := ih (update resource pair.1 pair.2 (pairValues cap resource pair.1 pair.2).value.total
        (if (compareLe (uniform (seed 0)).value (pairValues cap resource pair.1 pair.2).value.probability).value then
          (pairValues cap resource pair.1 pair.2).value.upper else (pairValues cap resource pair.1 pair.2).value.lower)).value
        (Fin.tail seed)
      rw [hu,hCompare,hControl]
      omega

theorem resourceLoop_value (cap : FixedArrayTable 3 ℝ) (C : ℕ) (resource : FixedArrayTable 3 ℝ)
    (seed : Fin C → ℝ) (fallback : Allocation 3) :
    (resourceLoop cap C resource seed).value.read =
      (roundResources cap.read (selectThreePair cap.read) C resource.read).realChoice.output C fallback seed := by
  induction C generalizing resource with
  | zero => rfl
  | succ C ih =>
    unfold resourceLoop
    dsimp only
    rw [selectedPair_complete]
    unfold roundResources
    by_cases h : 1 < (fractionalSet cap.read resource.read).card
    · simp only [dite_eq_left h,join_value,RoundingTree.realChoice]
      rw [RealChoiceTree.output_fork_succ]
      let selected := selectThreePair cap.read resource.read h
      let p := resourcePair cap.read resource.read selected.i selected.j selected.interior_i selected.interior_j
      have hp := pairValues_value cap resource selected.i selected.j selected.interior_i selected.interior_j
      change (pairValues cap resource selected.i selected.j).value = ⟨p.total,p.lower,p.upper,p.probability⟩ at hp
      change (resourceLoop cap C (update resource selected.i selected.j
        (pairValues cap resource selected.i selected.j).value.total
        (if (compareLe (uniform (seed 0)).value (pairValues cap resource selected.i selected.j).value.probability).value then
          (pairValues cap resource selected.i selected.j).value.upper else (pairValues cap resource selected.i selected.j).value.lower)).value
        (Fin.tail seed)).value.read = RealThresholdChoice.sample p.probability
          ((roundResources cap.read (selectThreePair cap.read) C (updatePair resource.read selected.i selected.j p.upper)).realChoice.output C fallback (Fin.tail seed))
          ((roundResources cap.read (selectThreePair cap.read) C (updatePair resource.read selected.i selected.j p.lower)).realChoice.output C fallback (Fin.tail seed)) (seed 0)
      rw [hp]
      simp only [uniform,Operation.realValue,compareLe,RealThresholdChoice.sample]
      by_cases hCoin : seed 0 ≤ p.probability
      · simp [hCoin]
        rw [ih]
        have hUpdate := update_value resource selected.i selected.j selected.distinct p.upper
        change (update resource selected.i selected.j p.total p.upper).value.read = _ at hUpdate
        rw [hUpdate]
      · simp [hCoin]
        rw [ih]
        have hUpdate := update_value resource selected.i selected.j selected.distinct p.lower
        change (update resource selected.i selected.j p.total p.lower).value.read = _ at hUpdate
        rw [hUpdate]
    · simp [h,join_value,RoundingTree.realChoice,RealChoiceTree.output,RealChoiceTree.sample]

noncomputable def capacityTable (long short : FixedArrayTable 3 ℝ) : Run (FixedArrayTable 3 ℝ) :=
  arrayRun 3 (fun j =>
    let L := loadReal long j
    let S := loadReal short j
    join L (join S (arithmetic .sub L.value S.value)))

theorem capacityTable_value (long short : FixedArrayTable 3 ℝ) :
    (capacityTable long short).value.read = fun j => long.read j - short.read j := by
  funext j
  simp [capacityTable,arrayRun_read,join_value,loadReal,arithmetic,Operation.realValue,RealArithmeticOp.apply]

theorem capacityTable_cost (long short : FixedArrayTable 3 ℝ) : (capacityTable long short).cost ≤ 17 := by
  apply arrayRun_bound 3 3
  intro j
  rw [join_cost,join_cost]
  change 1 + (1 + 1) ≤ 3
  decide

noncomputable def terminalFocus (cap resource : FixedArrayTable 3 ℝ) : Run (Fin 3) :=
  let flags := arrayRun 3 (fractionalProbe cap resource)
  join flags ⟨if flags.value.read 0 then 0 else if flags.value.read 1 then 1 else 2,[.control,.control]⟩

theorem terminalFocus_value (cap resource : FixedArrayTable 3 ℝ) (t : TerminalResources)
    (hCap : cap.read = t.capacity) (hR : resource.read = t.resource) : (terminalFocus cap resource).value = t.focus := by
  simp only [terminalFocus,join_value,arrayRun_read,fractionalProbe_value,hCap,hR,decide_eq_true_eq,TerminalResources.focus]

theorem terminalFocus_cost (cap resource : FixedArrayTable 3 ℝ) : (terminalFocus cap resource).cost ≤ 26 := by
  have hf := arrayRun_bound 3 5 (fractionalProbe cap resource) (fractionalProbe_cost cap resource)
  unfold terminalFocus
  rw [join_cost]
  change _ + 2 ≤ 26
  omega

noncomputable def terminalEndpoints (long short resource : FixedArrayTable 3 ℝ) : Run (FixedArrayTable 3 ℝ) :=
  arrayRun 3 (fun j =>
    let r := loadReal resource j
    let zero := compareLe r.value 0
    let cell := if zero.value then loadReal long j else loadReal short j
    join r (join zero (join (⟨(),[.control]⟩ : Run Unit) cell)))

theorem terminalEndpoints_value (long short resource : FixedArrayTable 3 ℝ) (t : TerminalResources)
    (hL : long.read = t.long) (hS : short.read = t.short) (hR : resource.read = t.resource) :
    (terminalEndpoints long short resource).value.read = t.endpoint := by
  funext j
  simp only [terminalEndpoints,arrayRun_read,join_value,loadReal,Operation.realValue,compareLe,hL,hS,hR,decide_eq_true_eq]
  by_cases hz : t.resource j = 0
  · simp [hz,TerminalResources.endpoint]
  · have hn : ¬ t.resource j ≤ 0 := not_le.mpr (lt_of_le_of_ne (t.box j).1 (Ne.symm hz))
    simp [hz,hn,TerminalResources.endpoint]

theorem terminalEndpoints_cost (long short resource : FixedArrayTable 3 ℝ) :
    (terminalEndpoints long short resource).cost ≤ 20 := by
  apply arrayRun_bound 3 4
  intro j
  rw [join_cost,join_cost,join_cost]
  change 1 + (1 + (1 + _)) ≤ 4
  split <;> change 1 + (1 + (1 + 1)) ≤ 4 <;> decide

noncomputable def specFields (i : NestedSpec) : FixedArrayTable 6 ℝ := FixedArrayTable.ofFn ![i.M,i.a,i.d,i.c,i.t,i.q]

noncomputable def storedNestedSpec (old : NestedSpec) (env : FixedArrayTable 6 ℝ) (h : env = specFields old) : NestedSpec where
  M := env.read 0
  a := env.read 1
  d := env.read 2
  c := env.read 3
  t := env.read 4
  q := env.read 5
  a_pos := by simpa [h,specFields,FixedArrayTable.read_ofFn] using old.a_pos
  d_pos := by simpa [h,specFields,FixedArrayTable.read_ofFn] using old.d_pos
  c_pos := by simpa [h,specFields,FixedArrayTable.read_ofFn] using old.c_pos
  t_pos := by simpa [h,specFields,FixedArrayTable.read_ofFn] using old.t_pos
  t_lt := by simpa [h,specFields,FixedArrayTable.read_ofFn] using old.t_lt
  q_nonneg := by simpa [h,specFields,FixedArrayTable.read_ofFn] using old.q_nonneg
  q_le := by simpa [h,specFields,FixedArrayTable.read_ofFn] using old.q_le
  a_le := by simpa [h,specFields,FixedArrayTable.read_ofFn] using old.a_le
  d_le := by simpa [h,specFields,FixedArrayTable.read_ofFn] using old.d_le
  c_le := by simpa [h,specFields,FixedArrayTable.read_ofFn] using old.c_le
  balance := by simpa [h,specFields,FixedArrayTable.read_ofFn] using old.balance

theorem storedNestedSpec_value (old : NestedSpec) (env : FixedArrayTable 6 ℝ) (h : env = specFields old) :
    storedNestedSpec old env h = old := by
  cases h
  rfl

noncomputable def terminalInput (t : TerminalResources) : Run NestedSpec :=
  let L := copyRow t.long
  let S := copyRow t.short
  let R := copyRow t.resource
  let cap := capacityTable L.value S.value
  let focus := terminalFocus cap.value R.value
  let endpoints := terminalEndpoints L.value S.value R.value
  let r := loadReal R.value focus.value
  let c := loadReal cap.value focus.value
  let probability := arithmetic .div r.value c.value
  let fields := copyRow ![t.M,endpoints.value.read (Equiv.swap focus.value 2 0),endpoints.value.read (Equiv.swap focus.value 2 1),
    L.value.read focus.value,S.value.read focus.value,probability.value]
  have hCap : cap.value.read = t.capacity := by
    simp only [cap,capacityTable_value,L,S,copyRow_read]
    rfl
  have hFocus : focus.value = t.focus := terminalFocus_value cap.value R.value t hCap (copyRow_read _)
  have hEnd : endpoints.value.read = t.endpoint := terminalEndpoints_value L.value S.value R.value t (copyRow_read _) (copyRow_read _) (copyRow_read _)
  have hFields : fields.value = specFields t.input := by
    apply table_ext
    intro j
    simp only [fields,r,c,probability,copyRow_read,hFocus,hEnd,L,S,R,copyRow_read,loadReal,Operation.realValue,arithmetic,
      RealArithmeticOp.apply,hCap,specFields,FixedArrayTable.read_ofFn,TerminalResources.input,
      TerminalResources.permutation,TerminalResources.weight]
  join L <| join S <| join R <| join cap <| join focus <| join endpoints <| join r <| join c <| join probability <|
    join fields ⟨storedNestedSpec t.input fields.value hFields,[.control,.control]⟩

theorem terminalInput_value (t : TerminalResources) : (terminalInput t).value = t.input := by
  simp only [terminalInput,join_value,storedNestedSpec_value]

theorem terminalInput_cost (t : TerminalResources) : (terminalInput t).cost ≤ 150 := by
  have hL := copyRow_cost t.long
  have hS := copyRow_cost t.short
  have hR := copyRow_cost t.resource
  have hCap := capacityTable_cost (copyRow t.long).value (copyRow t.short).value
  have hFocus := terminalFocus_cost (capacityTable (copyRow t.long).value (copyRow t.short).value).value (copyRow t.resource).value
  have hEnd := terminalEndpoints_cost (copyRow t.long).value (copyRow t.short).value (copyRow t.resource).value
  unfold terminalInput
  rw [join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost]
  have hLoad : ∀ (table : FixedArrayTable 3 ℝ) (j : Fin 3), (loadReal table j).cost = 1 := fun _ _ => rfl
  have hDiv : ∀ x y : ℝ, (arithmetic .div x y).cost = 1 := fun _ _ => rfl
  have hControl : ∀ value : NestedSpec, (⟨value,[Operation.control,.control]⟩ : Run NestedSpec).cost = 2 := fun _ => rfl
  simp only [copyRow_cost,hLoad,hDiv,hControl]
  omega

/-- Materialization from a retained finite address map. Its production is
priced separately by terminalPermutation and sortPermutation at the actual
fixed dimensions used below. -/
noncomputable def permuteRow {n : ℕ} (π : Equiv.Perm (Fin n)) (row : FixedArrayTable n ℝ) : Run (FixedArrayTable n ℝ) :=
  arrayRun n (fun j => join (⟨(),[.control]⟩ : Run Unit) (loadReal row (π j)))

theorem permuteRow_value {n : ℕ} (π : Equiv.Perm (Fin n)) (row : FixedArrayTable n ℝ) :
    (permuteRow π row).value.read = permuteAllocation π row.read := by
  funext j
  simp [permuteRow,arrayRun_read,join_value,loadReal,Operation.realValue,permuteAllocation]

theorem permuteRow_cost {n : ℕ} (π : Equiv.Perm (Fin n)) (row : FixedArrayTable n ℝ) :
    (permuteRow π row).cost ≤ 4 * n + 2 := by
  exact (arrayRun_bound n 2 _ (fun _ => by rw [join_cost]; change 1 + 1 ≤ 2; decide)).trans_eq (by omega)

noncomputable def terminalPermutation (t : TerminalResources) : Run (Equiv.Perm (Fin 3)) :=
  let L := copyRow t.long
  let S := copyRow t.short
  let R := copyRow t.resource
  let cap := capacityTable L.value S.value
  let focus := terminalFocus cap.value R.value
  join L (join S (join R (join cap (join focus ⟨Equiv.swap focus.value 2,[.control]⟩))))

theorem terminalPermutation_value (t : TerminalResources) : (terminalPermutation t).value = t.permutation := by
  have hC : (capacityTable (copyRow t.long).value (copyRow t.short).value).value.read = t.capacity := by
    rw [capacityTable_value]
    simp only [copyRow_read]
    rfl
  have hF := terminalFocus_value (capacityTable (copyRow t.long).value (copyRow t.short).value).value
    (copyRow t.resource).value t hC (copyRow_read _)
  simp only [terminalPermutation,join_value,hF,TerminalResources.permutation]

theorem terminalPermutation_cost (t : TerminalResources) : (terminalPermutation t).cost ≤ 100 := by
  have hC := capacityTable_cost (copyRow t.long).value (copyRow t.short).value
  have hF := terminalFocus_cost (capacityTable (copyRow t.long).value (copyRow t.short).value).value (copyRow t.resource).value
  unfold terminalPermutation
  rw [join_cost,join_cost,join_cost,join_cost,join_cost]
  simp only [copyRow_cost]
  change 11 + (11 + (11 + (_ + (_ + 1)))) ≤ 100
  omega

noncomputable def terminalDraw (t : TerminalResources) (seed : Fin 11 → ℝ) : Run (FixedArrayTable 3 ℝ) :=
  let input := terminalInput t
  let permutation := terminalPermutation t
  let result := nestedSpecDraw input.value seed
  join input (join permutation (join result (permuteRow permutation.value result.value)))

theorem terminalDraw_value (t : TerminalResources) (seed : Fin 11 → ℝ) :
    (terminalDraw t seed).value.read = t.realSample seed := by
  simp only [terminalDraw,join_value,permuteRow_value,nestedSpecDraw_value,terminalInput_value,terminalPermutation_value,TerminalResources.realSample]

theorem terminalDraw_cost (t : TerminalResources) (seed : Fin 11 → ℝ) : (terminalDraw t seed).cost ≤ 9800 := by
  have hi := terminalInput_cost t
  have ht := terminalPermutation_cost t
  have hd := nestedSpecDraw_cost (terminalInput t).value seed
  have hp := permuteRow_cost (terminalPermutation t).value (nestedSpecDraw (terminalInput t).value seed).value
  unfold terminalDraw
  rw [join_cost,join_cost,join_cost]
  omega

noncomputable def resourcePhase (i : NestedResourceSystem) (seed : Fin 2 → ℝ) : Run (FixedArrayTable 3 ℝ) :=
  let L := copyRow i.long
  let S := copyRow i.short
  let R := copyRow i.initial
  let cap := capacityTable L.value S.value
  join L (join S (join R (join cap (resourceLoop cap.value 2 R.value seed))))

theorem resourcePhase_value (i : NestedResourceSystem) (seed : Fin 2 → ℝ) :
    (resourcePhase i seed).value.read = i.realPhase seed := by
  have hCap : (capacityTable (copyRow i.long).value (copyRow i.short).value).value.read = i.capacity := by
    rw [capacityTable_value]
    funext j
    rw [congrFun (copyRow_read i.long) j,congrFun (copyRow_read i.short) j]
    rfl
  simp only [resourcePhase,join_value]
  rw [resourceLoop_value _ _ _ _ i.initial,hCap,copyRow_read]
  rw [i.realPhase_refines]
  rfl

theorem resourcePhase_cost (i : NestedResourceSystem) (seed : Fin 2 → ℝ) : (resourcePhase i seed).cost ≤ 300 := by
  have hC := capacityTable_cost (copyRow i.long).value (copyRow i.short).value
  have hR := resourceLoop_cost (capacityTable (copyRow i.long).value (copyRow i.short).value).value 2 (copyRow i.initial).value seed
  unfold resourcePhase
  rw [join_cost,join_cost,join_cost,join_cost]
  simp only [copyRow_cost]
  omega

noncomputable def nestedResourceDraw (i : NestedResourceSystem) (seed : (Fin 2 → ℝ) × (Fin 11 → ℝ)) : Run (FixedArrayTable 3 ℝ) :=
  let resources := resourcePhase i seed.1
  have hr : i.Valid resources.value.read := by rw [resourcePhase_value]; exact i.realPhase_valid seed.1
  join resources (terminalDraw (i.terminal resources.value.read hr) seed.2)

theorem nestedResourceDraw_value (i : NestedResourceSystem) (seed : (Fin 2 → ℝ) × (Fin 11 → ℝ)) :
    (nestedResourceDraw i seed).value.read = i.realSample seed := by
  simp only [nestedResourceDraw,join_value,terminalDraw_value,resourcePhase_value,NestedResourceSystem.realSample]

theorem nestedResourceDraw_cost (i : NestedResourceSystem) (seed : (Fin 2 → ℝ) × (Fin 11 → ℝ)) :
    (nestedResourceDraw i seed).cost ≤ 10200 := by
  have hr := resourcePhase_cost i seed.1
  unfold nestedResourceDraw
  rw [join_cost]
  have hd := terminalDraw_cost (i.terminal (resourcePhase i seed.1).value.read
    (by rw [resourcePhase_value]; exact i.realPhase_valid seed.1)) seed.2
  omega

theorem nestedResourceDraw_law (i : NestedResourceSystem) :
    Measure.map (fun seed => (nestedResourceDraw i seed).value.read)
      (NestedResourceSystem.realInputLaw : Measure ((Fin 2 → ℝ) × (Fin 11 → ℝ))) = (i.law : Measure (Allocation 3)) := by
  have h : (fun seed => (nestedResourceDraw i seed).value.read) = i.realSample := funext (nestedResourceDraw_value i)
  rw [h]
  exact i.realSample_law

theorem nestedResourceDraw_fullBudget (i : NestedResourceSystem) (seed : (Fin 2 → ℝ) × (Fin 11 → ℝ))
    (h : ∀ j, 0 ≤ seed.2 j ∧ seed.2 j ≤ 1) : FullBudget i.M (nestedResourceDraw i seed).value.read := by
  rw [nestedResourceDraw_value]
  exact i.realSample_fullBudget seed h

noncomputable def splitRow (a d : ℝ) (row : FixedArrayTable 3 ℝ) : Run (FixedArrayTable 4 ℝ) :=
  let total := arithmetic .add a d
  let firstCoefficient := arithmetic .div a total.value
  let secondCoefficient := arithmetic .div d total.value
  let x := loadReal row 0
  let y := loadReal row 1
  let z := loadReal row 2
  let first := arithmetic .mul firstCoefficient.value x.value
  let second := arithmetic .mul secondCoefficient.value x.value
  join total <| join firstCoefficient <| join secondCoefficient <| join x <| join y <| join z <| join first <| join second <|
    copyRow ![first.value,second.value,y.value,z.value]

theorem splitRow_value (a d : ℝ) (row : FixedArrayTable 3 ℝ) :
    (splitRow a d row).value.read = splitFirstTwo a d row.read := by
  funext j
  simp [splitRow,join_value,copyRow_read,loadReal,arithmetic,Operation.realValue,RealArithmeticOp.apply,splitFirstTwo]

theorem splitRow_cost (a d : ℝ) (row : FixedArrayTable 3 ℝ) : (splitRow a d row).cost ≤ 30 := by
  unfold splitRow
  rw [join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,copyRow_cost]
  change 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 14))))))) ≤ 30
  decide

noncomputable def mergeDraw (i : MergeFourInput) (seed : Fin 9 → ℝ) : Run (FixedArrayTable 4 ℝ) :=
  let pairLength := arithmetic .add i.l0 i.l1
  have hPair : pairLength.value = i.l0 + i.l1 := rfl
  let old := i.childSpec
  let input : ThreeSpec := {old with
    a := pairLength.value
    a_pos := by rw [hPair]; exact old.a_pos
    a_le := by rw [hPair]; exact old.a_le
    balance := by rw [hPair]; exact old.balance}
  let drawn := threeDraw input seed
  join pairLength (join drawn (splitRow i.l0 i.l1 drawn.value))

theorem mergeDraw_value (i : MergeFourInput) (seed : Fin 9 → ℝ) :
    (mergeDraw i seed).value.read = i.realSample seed := by
  simp only [mergeDraw,join_value,splitRow_value,threeDraw_value,MergeFourInput.realSample]
  rfl

theorem mergeDraw_cost (i : MergeFourInput) (seed : Fin 9 → ℝ) : (mergeDraw i seed).cost ≤ 7200 := by
  have hd := threeDraw_cost i.childSpec seed
  have hs := splitRow_cost i.l0 i.l1 (threeDraw i.childSpec seed).value
  unfold mergeDraw
  rw [join_cost,join_cost]
  change 1 + ((threeDraw i.childSpec seed).cost + (splitRow i.l0 i.l1 (threeDraw i.childSpec seed).value).cost) ≤ 7200
  omega

noncomputable def smallUniformFactory (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) : Run MergeFourInput :=
  let params := fourParameters i
  let scale := loadReal params.value.table 5
  let first := arithmetic .mul scale.value i.u
  let second := arithmetic .mul scale.value i.v
  let third := arithmetic .mul scale.value i.w
  let old := params.value.smallUniformInput hcase
  have h0 : first.value = old.l0 := rfl
  have h1 : second.value = old.l1 := rfl
  have h2 : third.value = old.l2 := rfl
  let produced : MergeFourInput := {old with
    l0 := first.value
    l1 := second.value
    l2 := third.value
    l0_pos := by rw [h0]; exact old.l0_pos
    l1_pos := by rw [h1]; exact old.l1_pos
    l2_pos := by rw [h2]; exact old.l2_pos
    pair_le := by rw [h0,h1]; exact old.pair_le
    l2_le := by rw [h2]; exact old.l2_le
    balance := by rw [h0,h1,h2]; exact old.balance}
  join params <| join scale <| join first <| join second <| join third <|
    ⟨produced,[.storeCell 0,.storeCell 1,.storeCell 2,.storeCell 3,.storeCell 4,.control]⟩

theorem smallUniformFactory_value (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    (smallUniformFactory i hcase).value = i.smallUniformInput hcase := by
  have hOld : (smallUniformFactory i hcase).value = (fourParameters i).value.smallUniformInput hcase := by
    rfl
  rw [hOld,RealFourParameterTable.smallUniformInput_eq]

theorem smallUniformFactory_cost (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    (smallUniformFactory i hcase).cost ≤ 4300 := by
  have hp := fourParameters_cost i
  unfold smallUniformFactory
  rw [join_cost,join_cost,join_cost,join_cost,join_cost]
  change (fourParameters i).cost + (1 + (1 + (1 + (1 + 6)))) ≤ 4300
  omega

noncomputable def smallUniformDraw (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (seed : (Fin 2 → ℝ) × (Fin 11 → ℝ)) : Run (FixedArrayTable 4 ℝ) :=
  let input := smallUniformFactory i hcase
  join input (mergeDraw input.value (RealUniformInputs.dropInputs 9 2 seed.2))

theorem smallUniformDraw_value (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (seed : (Fin 2 → ℝ) × (Fin 11 → ℝ)) : (smallUniformDraw i hcase seed).value.read = i.realSmallUniformSample hcase seed := by
  simp only [smallUniformDraw,join_value,mergeDraw_value,smallUniformFactory_value]
  rw [i.realSmallUniformSample_refines hcase]

theorem smallUniformDraw_cost (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (seed : (Fin 2 → ℝ) × (Fin 11 → ℝ)) : (smallUniformDraw i hcase seed).cost ≤ 12000 := by
  have hp := smallUniformFactory_cost i hcase
  have hd := mergeDraw_cost (smallUniformFactory i hcase).value (RealUniformInputs.dropInputs 9 2 seed.2)
  unfold smallUniformDraw
  rw [join_cost]
  omega

noncomputable def reflectedFactory (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) : Run NestedResourceSystem :=
  let params := fourParameters i
  let L := copyRow i.originalLengths
  let fraction := loadReal params.value.table 4
  let scale := loadReal params.value.table 5
  let probability := loadReal params.value.table 6
  let base := arithmetic .mul probability.value scale.value
  let S := arrayRun 3 (fun j =>
    let length := loadReal L.value j
    join length (arithmetic .mul fraction.value length.value))
  let R := arrayRun 3 (fun j =>
    let length := loadReal L.value j
    join length (arithmetic .mul base.value length.value))
  let old := params.value.reflectedResourceSystem hcase
  have hS : S.value.read = old.short := by
    funext j
    simp [S,old,arrayRun_read,join_value,loadReal,arithmetic,Operation.realValue,RealArithmeticOp.apply,L,copyRow_read,
      fraction,RealFourParameterTable.reflectedResourceSystem,RealFourParameterTable.shortFraction]
  have hR : R.value.read = old.initial := by
    funext j
    simp [R,old,arrayRun_read,join_value,loadReal,arithmetic,Operation.realValue,RealArithmeticOp.apply,L,copyRow_read,
      base,scale,probability,RealFourParameterTable.reflectedResourceSystem,
      RealFourParameterTable.nestedProbability,RealFourParameterTable.scaleFraction]
  let produced : NestedResourceSystem := {old with
    short := S.value.read
    initial := R.value.read
    short_pos := by rw [hS]; exact old.short_pos
    short_lt := by rw [hS]; exact old.short_lt
    initial_box := by rw [hS,hR]; exact old.initial_box
    initial_mean := by rw [hR]; exact old.initial_mean}
  join params <| join L <| join fraction <| join scale <| join probability <| join base <| join S <| join R <|
    ⟨produced,[.control,.control]⟩

theorem reflectedFactory_value (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    (reflectedFactory i hcase).value = i.reflectedResourceSystem hcase := by
  unfold reflectedFactory
  simp only [join_value]
  have h := (fourParameters i).value.reflectedResourceSystem_eq hcase
  apply Eq.trans _ h
  apply NestedResourceSystem.eq_of_data
  · rfl
  · rfl
  · funext j
    simp [arrayRun_read,join_value,loadReal,arithmetic,Operation.realValue,RealArithmeticOp.apply,copyRow_read,
      RealFourParameterTable.reflectedResourceSystem,RealFourParameterTable.shortFraction]
  · funext j
    simp [arrayRun_read,join_value,loadReal,arithmetic,Operation.realValue,RealArithmeticOp.apply,copyRow_read,
      RealFourParameterTable.reflectedResourceSystem,RealFourParameterTable.nestedProbability,RealFourParameterTable.scaleFraction]

theorem reflectedFactory_cost (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    (reflectedFactory i hcase).cost ≤ 4400 := by
  have hp := fourParameters_cost i
  have hBody : ∀ (coefficient : ℝ) (table : FixedArrayTable 3 ℝ) (j : Fin 3),
      (join (loadReal table j) (arithmetic .mul coefficient (loadReal table j).value)).cost ≤ 2 := by
    intro _ _ _
    rw [join_cost]
    change 1 + 1 ≤ 2
    decide
  have hArray : ∀ (coefficient : ℝ) (table : FixedArrayTable 3 ℝ),
      (arrayRun 3 (fun j => join (loadReal table j) (arithmetic .mul coefficient (loadReal table j).value))).cost ≤ 14 := by
    intro coefficient table
    exact arrayRun_bound 3 2 _ (hBody coefficient table)
  unfold reflectedFactory
  rw [join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,copyRow_cost]
  have hS := hArray (loadReal (fourParameters i).value.table 4).value (copyRow i.originalLengths).value
  have hR := hArray (arithmetic .mul (loadReal (fourParameters i).value.table 6).value (loadReal (fourParameters i).value.table 5).value).value
    (copyRow i.originalLengths).value
  change (fourParameters i).cost + (11 + (1 + (1 + (1 + (1 + (_ + (_ + 2))))))) ≤ 4400
  dsimp only
  omega

noncomputable def reflectRow (length : Allocation 3) (row : FixedArrayTable 3 ℝ) : Run (FixedArrayTable 4 ℝ) :=
  let L := copyRow length
  let first := arrayRun 3 (fun j =>
    let l := loadReal L.value j
    let r := loadReal row j
    join l (join r (arithmetic .sub l.value r.value)))
  join L (join first (copyRow ![first.value.read 0,first.value.read 1,first.value.read 2,0]))

theorem reflectRow_value (length : Allocation 3) (row : FixedArrayTable 3 ℝ) :
    (reflectRow length row).value.read = reflectAppend length row.read := by
  funext j
  simp [reflectRow,join_value,copyRow_read,arrayRun_read,loadReal,arithmetic,Operation.realValue,RealArithmeticOp.apply,reflectAppend]

theorem reflectRow_cost (length : Allocation 3) (row : FixedArrayTable 3 ℝ) : (reflectRow length row).cost ≤ 60 := by
  have hFirst := capacityTable_cost (copyRow length).value row
  unfold reflectRow
  rw [join_cost,join_cost]
  simp only [copyRow_cost]
  change 11 + ((capacityTable (copyRow length).value row).cost + 14) ≤ 60
  omega

noncomputable def reflectedDraw (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (seed : (Fin 2 → ℝ) × (Fin 11 → ℝ)) : Run (FixedArrayTable 4 ℝ) :=
  let input := reflectedFactory i hcase
  let drawn := nestedResourceDraw input.value seed
  join input (join drawn (reflectRow i.originalLengths drawn.value))

theorem reflectedDraw_value (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (seed : (Fin 2 → ℝ) × (Fin 11 → ℝ)) : (reflectedDraw i hcase seed).value.read = i.realReflectedSample hcase seed := by
  simp only [reflectedDraw,join_value,reflectRow_value,nestedResourceDraw_value,reflectedFactory_value]
  rw [i.realReflectedSample_refines hcase]
  rfl

theorem reflectedDraw_cost (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (seed : (Fin 2 → ℝ) × (Fin 11 → ℝ)) : (reflectedDraw i hcase seed).cost ≤ 15000 := by
  have hi := reflectedFactory_cost i hcase
  have hd := nestedResourceDraw_cost (reflectedFactory i hcase).value seed
  have hr := reflectRow_cost i.originalLengths (nestedResourceDraw (reflectedFactory i hcase).value seed).value
  unfold reflectedDraw
  rw [join_cost,join_cost]
  omega

noncomputable def smallDraw (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (seed : ℝ × ((Fin 2 → ℝ) × (Fin 11 → ℝ))) : Run (FixedArrayTable 4 ℝ) :=
  let u := uniform seed.1
  let compared := compareLe u.value i.p
  let selected := if compared.value then smallUniformDraw i hcase seed.2 else reflectedDraw i hcase seed.2
  join u (join compared (join (⟨(),[.control]⟩ : Run Unit) selected))

theorem smallDraw_value (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (seed : ℝ × ((Fin 2 → ℝ) × (Fin 11 → ℝ))) : (smallDraw i hcase seed).value.read = i.realSmallSample hcase seed := by
  by_cases h : seed.1 ≤ i.p
  · simp [smallDraw,join_value,uniform,Operation.realValue,compareLe,h,smallUniformDraw_value,FourInput.realSmallSample]
  · simp [smallDraw,join_value,uniform,Operation.realValue,compareLe,h,reflectedDraw_value,FourInput.realSmallSample]

theorem smallDraw_cost (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (seed : ℝ × ((Fin 2 → ℝ) × (Fin 11 → ℝ))) : (smallDraw i hcase seed).cost ≤ 15100 := by
  have hU := smallUniformDraw_cost i hcase seed.2
  have hR := reflectedDraw_cost i hcase seed.2
  unfold smallDraw
  rw [join_cost,join_cost,join_cost]
  change 1 + (1 + (1 + _)) ≤ 15100
  split <;> omega

noncomputable def fourDraw (i : FourInput) (seed : RealFourSeed) : Run (FixedArrayTable 4 ℝ) :=
  let complement := arithmetic .sub 1 i.p
  let regime := arithmetic .mul complement.value i.ell
  let compared := compareLe regime.value i.w
  have hRegime : regime.value = (1 - i.p) * i.ell := rfl
  let selected := if hcase : regime.value ≤ i.w then
    gluingDraw i (by simpa only [hRegime] using hcase) seed.1 else
      smallDraw i (by rw [← hRegime]; exact lt_of_not_ge hcase) seed.2
  join complement (join regime (join compared (join (⟨(),[.control]⟩ : Run Unit) selected)))

theorem fourDraw_value (i : FourInput) (seed : RealFourSeed) : (fourDraw i seed).value.read = i.realSample seed := by
  have hRegime : (arithmetic .mul (arithmetic .sub 1 i.p).value i.ell).value = (1 - i.p) * i.ell := rfl
  unfold fourDraw
  dsimp only
  simp only [join_value]
  by_cases hcase : (arithmetic .mul (arithmetic .sub 1 i.p).value i.ell).value ≤ i.w
  · simp only [dite_eq_left hcase]
    have hOriginal : (1 - i.p) * i.ell ≤ i.w := by simpa only [hRegime] using hcase
    rw [gluingDraw_value]
    simp only [FourInput.realSample,dite_eq_left hOriginal]
  · simp only [dite_eq_right hcase]
    have hOriginal : ¬ (1 - i.p) * i.ell ≤ i.w := by simpa only [hRegime] using hcase
    rw [smallDraw_value]
    simp only [FourInput.realSample,dite_eq_right hOriginal]

theorem fourDraw_cost (i : FourInput) (seed : RealFourSeed) : (fourDraw i seed).cost ≤ 426000 := by
  have hRegime : (arithmetic .mul (arithmetic .sub 1 i.p).value i.ell).value = (1 - i.p) * i.ell := rfl
  unfold fourDraw
  rw [join_cost,join_cost,join_cost,join_cost]
  change 1 + (1 + (1 + (1 + _))) ≤ 426000
  split
  · rename_i hcase
    have hd := gluingDraw_cost i (by simpa only [hRegime] using hcase) seed.1
    omega
  · rename_i hcase
    have hd := smallDraw_cost i (by rw [← hRegime]; exact lt_of_not_ge hcase) seed.2
    omega

theorem fourDraw_law (i : FourInput) :
    Measure.map (fun seed => (fourDraw i seed).value.read)
      (FourInput.realInputLaw : Measure RealFourSeed) = (i.law : Measure (Allocation 4)) := by
  have h : (fun seed => (fourDraw i seed).value.read) = i.realSample := funext (fourDraw_value i)
  rw [h]
  exact i.realSample_law

theorem fourDraw_fullBudget (i : FourInput) (seed : RealFourSeed)
    (hG : 0 ≤ seed.1 0 ∧ seed.1 0 ≤ 1) (hN : ∀ j, 0 ≤ seed.2.2.2 j ∧ seed.2.2.2 j ≤ 1) :
    FullBudget i.B (fourDraw i seed).value.read := by
  rw [fourDraw_value]
  exact i.realSample_fullBudget seed hG hN

noncomputable def compareIndices (row : FixedArrayTable 3 ℝ) (i j : Fin 3) : Run (Equiv.Perm (Fin 3)) :=
  let x := loadReal row i
  let y := loadReal row j
  let compared := compareLe x.value y.value
  join x (join y (join compared ⟨if compared.value then Equiv.refl _ else Equiv.swap i j,[.control,.control]⟩))

theorem compareIndices_value (row : FixedArrayTable 3 ℝ) (i j : Fin 3) :
    (compareIndices row i j).value = comparePermutation row.read i j := by
  by_cases h : row.read i ≤ row.read j <;>
    simp [compareIndices,join_value,loadReal,Operation.realValue,compareLe,comparePermutation,h]

theorem compareIndices_cost (row : FixedArrayTable 3 ℝ) (i j : Fin 3) : (compareIndices row i j).cost ≤ 5 := by
  unfold compareIndices
  rw [join_cost,join_cost,join_cost]
  change 1 + (1 + (1 + 2)) ≤ 5
  decide

noncomputable def sortPermutation (row : FixedArrayTable 3 ℝ) : Run (Equiv.Perm (Fin 3)) :=
  let p := compareIndices row 0 1
  let M := permuteRow p.value row
  let q := compareIndices M.value 1 2
  let N := permuteRow q.value M.value
  let r := compareIndices N.value 0 1
  join p (join M (join q (join N (join r ⟨(r.value.trans q.value).trans p.value,[.control,.control,.control]⟩))))

theorem sortPermutation_value (row : FixedArrayTable 3 ℝ) :
    (sortPermutation row).value = sortTriplePermutation row.read := by
  simp only [sortPermutation,join_value,compareIndices_value,permuteRow_value,sortTriplePermutation]

theorem sortPermutation_cost (row : FixedArrayTable 3 ℝ) : (sortPermutation row).cost ≤ 50 := by
  have hp := compareIndices_cost row 0 1
  have hM := permuteRow_cost (compareIndices row 0 1).value row
  have hq := compareIndices_cost (permuteRow (compareIndices row 0 1).value row).value 1 2
  have hN := permuteRow_cost (compareIndices (permuteRow (compareIndices row 0 1).value row).value 1 2).value
    (permuteRow (compareIndices row 0 1).value row).value
  have hr := compareIndices_cost (permuteRow (compareIndices (permuteRow (compareIndices row 0 1).value row).value 1 2).value
    (permuteRow (compareIndices row 0 1).value row).value).value 0 1
  unfold sortPermutation
  rw [join_cost,join_cost,join_cost,join_cost,join_cost]
  change _ + (_ + (_ + (_ + (_ + 3)))) ≤ 50
  omega

noncomputable def storedFour (old : FourInput) (env : FixedArrayTable 6 ℝ)
    (h : env = RealFourParametersCode.environment old) : FourInput where
  B := env.read 0
  u := env.read 1
  v := env.read 2
  w := env.read 3
  ell := env.read 4
  p := env.read 5
  u_pos := by simpa [h,RealFourParametersCode.environment,FixedArrayTable.read_ofFn] using old.u_pos
  uv := by simpa [h,RealFourParametersCode.environment,FixedArrayTable.read_ofFn] using old.uv
  vw := by simpa [h,RealFourParametersCode.environment,FixedArrayTable.read_ofFn] using old.vw
  ell_pos := by simpa [h,RealFourParametersCode.environment,FixedArrayTable.read_ofFn] using old.ell_pos
  p_pos := by simpa [h,RealFourParametersCode.environment,FixedArrayTable.read_ofFn] using old.p_pos
  p_lt := by simpa [h,RealFourParametersCode.environment,FixedArrayTable.read_ofFn] using old.p_lt
  w_le := by simpa [h,RealFourParametersCode.environment,FixedArrayTable.read_ofFn] using old.w_le
  ell_le := by simpa [h,RealFourParametersCode.environment,FixedArrayTable.read_ofFn] using old.ell_le
  balance := by simpa [h,RealFourParametersCode.environment,FixedArrayTable.read_ofFn] using old.balance

theorem storedFour_value (old : FourInput) (env : FixedArrayTable 6 ℝ)
    (h : env = RealFourParametersCode.environment old) : storedFour old env h = old := by
  cases h
  rfl

noncomputable def sortedFourInput (i : FourSpec) : Run (FourInput × Equiv.Perm (Fin 3)) :=
  let source := copyRow i.length
  let permutation := sortPermutation source.value
  let sorted := permuteRow permutation.value source.value
  let fields := copyRow ![i.B,sorted.value.read 0,sorted.value.read 1,sorted.value.read 2,i.ell,i.p]
  have hFields : fields.value = RealFourParametersCode.environment i.input := by
    apply table_ext
    intro j
    simp only [fields,copyRow_read,sorted,permuteRow_value,permutation,sortPermutation_value,source,copyRow_read,
      RealFourParametersCode.environment,FixedArrayTable.read_ofFn,FourSpec.input,sortedTriple]
  join source (join permutation (join sorted (join fields
    ⟨(storedFour i.input fields.value hFields,permutation.value),[.control,.control]⟩)))

theorem sortedFourInput_value (i : FourSpec) : (sortedFourInput i).value = (i.input,sortTriplePermutation i.length) := by
  simp only [sortedFourInput,join_value,storedFour_value,sortPermutation_value,copyRow_read]

theorem sortedFourInput_cost (i : FourSpec) : (sortedFourInput i).cost ≤ 110 := by
  have hp := sortPermutation_cost (copyRow i.length).value
  have hs := permuteRow_cost (sortPermutation (copyRow i.length).value).value (copyRow i.length).value
  unfold sortedFourInput
  rw [join_cost,join_cost,join_cost,join_cost]
  simp only [copyRow_cost]
  change 11 + (_ + (_ + (20 + 2))) ≤ 110
  omega

noncomputable def fourSpecDraw (i : FourSpec) (seed : RealFourSeed) : Run (FixedArrayTable 4 ℝ) :=
  let prepared := sortedFourInput i
  let drawn := fourDraw prepared.value.1 seed
  join prepared (join drawn (permuteRow (permutationWithLast prepared.value.2).symm drawn.value))

theorem fourSpecDraw_value (i : FourSpec) (seed : RealFourSeed) : (fourSpecDraw i seed).value.read = i.realSample seed := by
  simp only [fourSpecDraw,join_value,permuteRow_value,fourDraw_value,sortedFourInput_value,FourSpec.realSample]

theorem fourSpecDraw_cost (i : FourSpec) (seed : RealFourSeed) : (fourSpecDraw i seed).cost ≤ 427000 := by
  have hp := sortedFourInput_cost i
  have hd := fourDraw_cost (sortedFourInput i).value.1 seed
  have hr := permuteRow_cost (permutationWithLast (sortedFourInput i).value.2).symm
    (fourDraw (sortedFourInput i).value.1 seed).value
  unfold fourSpecDraw
  rw [join_cost,join_cost]
  omega

theorem fourSpecDraw_law (i : FourSpec) :
    Measure.map (fun seed => (fourSpecDraw i seed).value.read)
      (FourInput.realInputLaw : Measure RealFourSeed) = (i.law : Measure (Allocation 4)) := by
  have h : (fun seed => (fourSpecDraw i seed).value.read) = i.realSample := funext (fourSpecDraw_value i)
  rw [h]
  exact i.realSample_law

theorem fourSpecDraw_fullBudget (i : FourSpec) (seed : RealFourSeed)
    (hG : 0 ≤ seed.1 0 ∧ seed.1 0 ≤ 1) (hN : ∀ j, 0 ≤ seed.2.2.2 j ∧ seed.2.2.2 j ≤ 1) :
    FullBudget i.B (fourSpecDraw i seed).value.read := by
  rw [fourSpecDraw_value]
  exact i.realSample_fullBudget seed hG hN

end Blotto.RealPRGReflectedExecution
