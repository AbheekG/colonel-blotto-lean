import Blotto.RealPRGReflectedExecution
import Blotto.RealLottoActivePhase

/-! The global exact-real source in the declared mutable-cell RAM model.
The resource buffer is one fixed region; each selected store consumes the
current state and replaces its cells in that region. Lean arrays below are
denotations of that region, and do not assert host uniqueness or host in-place
Array.set cost. Read-only lengths and the maintained list are separate regions.
No discarded branch, old buffer snapshot, or untouched active tail is retained
by the machine transition. -/
namespace Blotto.RealPRGResourceExecution
open MeasureTheory PRGRealRAMExecution PRGExactRealRAMContract RealPRGNativeFactoryExecution
open scoped BigOperators Classical

noncomputable def tableOfBuffer {n : ℕ} (buffer : PairStoreBuffer n ℝ) : FixedArrayTable n ℝ := ⟨buffer.data,buffer.size⟩

@[simp] theorem tableOfBuffer_read {n : ℕ} (buffer : PairStoreBuffer n ℝ) (j : Fin n) :
    (tableOfBuffer buffer).read j = buffer.read j := rfl

noncomputable def loadRegister (n : ℕ) (registers : PairStoreBuffer 4 ℝ) (j : Fin 4) : Run ℝ :=
  ⟨registers.read j,[.load (n + j.val) (registers.read j)]⟩

theorem resource_register_address_disjoint {n : ℕ} (cell : Fin n) (register : Fin 4) :
    cell.val ≠ n + register.val := by omega

noncomputable def loadLength {n : ℕ} (length : FixedArrayTable n ℝ) (j : Fin n) : Run ℝ :=
  ⟨length.read j,[.load (n + 4 + j.val) (length.read j)]⟩

theorem resource_length_address_disjoint {n : ℕ} (cell j : Fin n) :
    cell.val ≠ n + 4 + j.val := by omega

theorem register_length_address_disjoint {n : ℕ} (register : Fin 4) (j : Fin n) :
    n + register.val ≠ n + 4 + j.val := by omega

noncomputable def storeInstruction {n : ℕ} : PairStoreInstruction n → PairStoreState n ℝ → Run (PairStoreState n ℝ)
  | .load cell destination, s =>
    let loaded := loadReal (tableOfBuffer s.cells) cell
    join loaded ⟨{s with registers := s.registers.write destination loaded.value},
      [.control,.storeCell (n + destination.val)]⟩
  | .add destination left right, s =>
    let first := loadRegister n s.registers left
    let second := loadRegister n s.registers right
    let result := arithmetic .add first.value second.value
    join first (join second (join result
      ⟨{s with registers := s.registers.write destination result.value},[.control,.storeCell (n + destination.val)]⟩))
  | .sub destination left right, s =>
    let first := loadRegister n s.registers left
    let second := loadRegister n s.registers right
    let result := arithmetic .sub first.value second.value
    join first (join second (join result
      ⟨{s with registers := s.registers.write destination result.value},[.control,.storeCell (n + destination.val)]⟩))
  | .store cell source, s =>
    let loaded := loadRegister n s.registers source
    join loaded ⟨{s with cells := s.cells.write cell loaded.value},[.store cell.val loaded.value,.control]⟩

theorem storeInstruction_value {n : ℕ} (instruction : PairStoreInstruction n) (s : PairStoreState n ℝ) :
    (storeInstruction instruction s).value = instruction.execute s := by
  cases instruction <;> rfl

theorem storeInstruction_cost {n : ℕ} (instruction : PairStoreInstruction n) (s : PairStoreState n ℝ) :
    (storeInstruction instruction s).cost ≤ 5 := by
  cases instruction with
  | load cell destination =>
    unfold storeInstruction
    rw [join_cost]
    change 1 + 2 ≤ 5
    decide
  | add destination left right | sub destination left right =>
    unfold storeInstruction
    rw [join_cost,join_cost,join_cost]
    change 1 + (1 + (1 + 2)) ≤ 5
    decide
  | store cell source =>
    unfold storeInstruction
    rw [join_cost]
    change 1 + 2 ≤ 5
    decide

noncomputable def storeProgram {n : ℕ} : List (PairStoreInstruction n) → PairStoreState n ℝ → Run (PairStoreState n ℝ)
  | [], s => ⟨s,[.control]⟩
  | instruction :: rest, s =>
    let next := storeInstruction instruction s
    join next (join (⟨(),[.control]⟩ : Run Unit) (storeProgram rest next.value))

theorem storeProgram_value {n : ℕ} (code : List (PairStoreInstruction n)) (s : PairStoreState n ℝ) :
    (storeProgram code s).value = PairStoreProgram.run code s := by
  induction code generalizing s with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [storeProgram,join_value,storeInstruction_value,PairStoreProgram.run,ih]

theorem storeProgram_cost {n : ℕ} (code : List (PairStoreInstruction n)) (s : PairStoreState n ℝ) :
    (storeProgram code s).cost ≤ 6 * code.length + 1 := by
  induction code generalizing s with
  | nil => simp [storeProgram,Run.cost,Operation.cost]
  | cons instruction rest ih =>
    have hs := storeInstruction_cost instruction s
    have hl := ih (storeInstruction instruction s).value
    unfold storeProgram
    rw [join_cost,join_cost]
    change _ + (1 + _) ≤ _
    simp only [List.length_cons]
    omega

theorem storeProgram_regions {n : ℕ} (code : List (PairStoreInstruction n)) (s : PairStoreState n ℝ) :
    (storeProgram code s).value.cells.data.size = n ∧
      (storeProgram code s).value.registers.data.size = 4 := by
  rw [storeProgram_value]
  exact PairStoreProgram.region_sizes code s

noncomputable def storePair {n : ℕ} (resource : ResourceArray n) (a b : Fin n) (first : ℝ) : Run (ResourceArray n) :=
  let registers := copyRow ![first,0,0,0]
  let machine : PairStoreState n ℝ := ⟨⟨resource.data,resource.size⟩,⟨registers.value.data,registers.value.size⟩⟩
  let result := storeProgram (PairStoreProgram.code a b) machine
  join registers (join result ⟨⟨result.value.cells.data,result.value.cells.size⟩,[.control]⟩)

theorem storePair_value {n : ℕ} (resource : ResourceArray n) (a b : Fin n) (first : ℝ) :
    (storePair resource a b first).value = resource.updatePair a b first := by
  simp only [storePair,join_value,storeProgram_value]
  rfl

theorem storePair_cost {n : ℕ} (resource : ResourceArray n) (a b : Fin n) (first : ℝ) :
    (storePair resource a b first).cost ≤ 55 := by
  unfold storePair
  rw [join_cost,join_cost,copyRow_cost]
  have hp := storeProgram_cost (PairStoreProgram.code a b)
    (⟨⟨resource.data,resource.size⟩,⟨(copyRow ![first,0,0,0]).value.data,(copyRow ![first,0,0,0]).value.size⟩⟩ : PairStoreState n ℝ)
  have hCode : (PairStoreProgram.code a b).length = 6 := rfl
  rw [hCode] at hp
  change 14 + (_ + 1) ≤ 55
  omega

noncomputable def fractionalProbe {n : ℕ} (length : FixedArrayTable n ℝ) (resource : ResourceArray n) (j : Fin n) : Run Bool :=
  let L := loadLength length j
  let R := loadReal (⟨resource.data,resource.size⟩ : FixedArrayTable n ℝ) j
  let lower := RealPRGNativeFactoryExecution.compareLt 0 R.value
  let upper := RealPRGNativeFactoryExecution.compareLt R.value L.value
  join L (join R (join lower (join upper ⟨lower.value && upper.value,[.control]⟩)))

theorem fractionalProbe_value {n : ℕ} (length : FixedArrayTable n ℝ) (resource : ResourceArray n) (j : Fin n) :
    (fractionalProbe length resource j).value = decide (Fractional length.read resource.allocation j) := by
  simp only [fractionalProbe,join_value,loadReal,loadLength,Operation.realValue,RealPRGNativeFactoryExecution.compareLt]
  change (decide (0 < resource.allocation j) && decide (resource.allocation j < length.read j)) =
    decide (Fractional length.read resource.allocation j)
  by_cases hL : 0 < resource.allocation j <;> by_cases hU : resource.allocation j < length.read j <;>
    simp [Fractional,hL,hU]

theorem fractionalProbe_cost {n : ℕ} (length : FixedArrayTable n ℝ) (resource : ResourceArray n) (j : Fin n) :
    (fractionalProbe length resource j).cost ≤ 5 := by
  unfold fractionalProbe
  rw [join_cost,join_cost,join_cost,join_cost]
  change 1 + (1 + (1 + (1 + 1))) ≤ 5
  decide

noncomputable def activeScan {n : ℕ} (length : FixedArrayTable n ℝ) (resource : ResourceArray n) : List (Fin n) → Run (List (Fin n))
  | [] => ⟨[],[.control]⟩
  | j :: rest =>
    let flag := fractionalProbe length resource j
    let later := activeScan length resource rest
    let result := if flag.value then j :: later.value else later.value
    join flag (join later ⟨result,[.control,.control,.storeCell j.val]⟩)

theorem activeScan_value {n : ℕ} (length : FixedArrayTable n ℝ) (resource : ResourceArray n) (items : List (Fin n)) :
    (activeScan length resource items).value = items.filter (fun j => decide (Fractional length.read resource.allocation j)) := by
  induction items with
  | nil => rfl
  | cons j rest ih =>
    simp only [activeScan,join_value,fractionalProbe_value,ih,List.filter_cons]

theorem activeScan_cost {n : ℕ} (length : FixedArrayTable n ℝ) (resource : ResourceArray n) (items : List (Fin n)) :
    (activeScan length resource items).cost ≤ 8 * items.length + 1 := by
  induction items with
  | nil => simp [activeScan,Run.cost,Operation.cost]
  | cons j rest ih =>
    have hf := fractionalProbe_cost length resource j
    unfold activeScan
    rw [join_cost,join_cost]
    change _ + (_ + 3) ≤ _
    simp only [List.length_cons]
    omega

noncomputable def pairValues {n : ℕ} (length : FixedArrayTable n ℝ) (resource : ResourceArray n)
    (i j : Fin n) : Run RealPRGReflectedExecution.PairValues :=
  let li := loadLength length i
  let lj := loadLength length j
  let ri := loadReal (⟨resource.data,resource.size⟩ : FixedArrayTable n ℝ) i
  let rj := loadReal (⟨resource.data,resource.size⟩ : FixedArrayTable n ℝ) j
  let total := arithmetic .add ri.value rj.value
  let candidate := arithmetic .sub total.value lj.value
  let lower := arithmetic .maximum 0 candidate.value
  let upper := arithmetic .minimum li.value total.value
  let numerator := arithmetic .sub ri.value lower.value
  let denominator := arithmetic .sub upper.value lower.value
  let probability := arithmetic .div numerator.value denominator.value
  join li <| join lj <| join ri <| join rj <| join total <| join candidate <| join lower <| join upper <|
    join numerator <| join denominator <| join probability <|
      ⟨⟨total.value,lower.value,upper.value,probability.value⟩,[.storeCell n,.storeCell (n+1),.storeCell (n+2),.storeCell (n+3)]⟩

theorem pairValues_value {n : ℕ} (length : FixedArrayTable n ℝ) (resource : ResourceArray n)
    (i j : Fin n) (hi : Fractional length.read resource.allocation i) (hj : Fractional length.read resource.allocation j) :
    let p := resourcePair length.read resource.allocation i j hi hj
    (pairValues length resource i j).value = ⟨p.total,p.lower,p.upper,p.probability⟩ := by
  rfl

theorem pairValues_cost {n : ℕ} (length : FixedArrayTable n ℝ) (resource : ResourceArray n) (i j : Fin n) :
    (pairValues length resource i j).cost ≤ 20 := by
  unfold pairValues
  rw [join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost,join_cost]
  change 1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (1 + 4)))))))))) ≤ 20
  decide

noncomputable def prependActive {n : ℕ} : List (Fin n) → List (Fin n) → Run (List (Fin n))
  | [], tail => ⟨tail,[.control]⟩
  | head :: rest, tail =>
    let later := prependActive rest tail
    join later ⟨head :: later.value,[.control,.storeCell head.val,.control]⟩

theorem prependActive_value {n : ℕ} (front tail : List (Fin n)) :
    (prependActive front tail).value = front ++ tail := by
  induction front with
  | nil => rfl
  | cons head rest ih => simp [prependActive,join_value,ih]

theorem prependActive_cost {n : ℕ} (front tail : List (Fin n)) :
    (prependActive front tail).cost ≤ 3 * front.length + 1 := by
  induction front with
  | nil => simp [prependActive,Run.cost,Operation.cost]
  | cons head rest ih =>
    unfold prependActive
    rw [join_cost]
    change _ + 3 ≤ _
    simp only [List.length_cons]
    omega

theorem arrayState_ext {n : ℕ} {L : Allocation n} (s t : ArrayResourceState L)
    (hR : s.resource = t.resource) (hA : s.active = t.active) : s = t := by
  cases s
  cases t
  cases hR
  cases hA
  rfl

noncomputable def arrayUpdate {n : ℕ} {L : Allocation n} (length : FixedArrayTable n ℝ)
    (hL : length.read = L) (s : ArrayResourceState L) (a b : Fin n) (tail : List (Fin n))
    (he : s.active = a :: b :: tail) (z : ℝ) : Run (ArrayResourceState L) :=
  let stored := storePair s.resource a b z
  let addresses : Run (List (Fin n)) := ⟨[a,b],[.storeCell a.val,.storeCell b.val,.control]⟩
  let retained := activeScan length stored.value addresses.value
  let active := prependActive retained.value tail
  have hResource : stored.value = (s.realUpdate a b tail he z).resource := storePair_value _ _ _ _
  have hActive : active.value = (s.realUpdate a b tail he z).active := by
    simp only [active,prependActive_value,retained,addresses,activeScan_value,hL,stored,storePair_value,
      ArrayResourceState.realUpdate,retainedPair]
  let produced : ArrayResourceState L :=
    ⟨stored.value,active.value,
      by rw [hActive]; exact (s.realUpdate a b tail he z).nodup,
      by rw [hActive,hResource]; exact (s.realUpdate a b tail he z).membership⟩
  join stored (join addresses (join retained (join active ⟨produced,[.control]⟩)))

theorem arrayUpdate_value {n : ℕ} {L : Allocation n} (length : FixedArrayTable n ℝ)
    (hL : length.read = L) (s : ArrayResourceState L) (a b : Fin n) (tail : List (Fin n))
    (he : s.active = a :: b :: tail) (z : ℝ) :
    (arrayUpdate length hL s a b tail he z).value = s.realUpdate a b tail he z := by
  apply arrayState_ext
  · simp only [arrayUpdate,join_value,storePair_value,ArrayResourceState.realUpdate]
  · simp only [arrayUpdate,join_value,prependActive_value,activeScan_value,hL,storePair_value,
      ArrayResourceState.realUpdate,retainedPair]

theorem arrayUpdate_cost {n : ℕ} {L : Allocation n} (length : FixedArrayTable n ℝ)
    (hL : length.read = L) (s : ArrayResourceState L) (a b : Fin n) (tail : List (Fin n))
    (he : s.active = a :: b :: tail) (z : ℝ) :
    (arrayUpdate length hL s a b tail he z).cost ≤ 85 := by
  have hs := storePair_cost s.resource a b z
  have hr := activeScan_cost length (storePair s.resource a b z).value [a,b]
  have hLen : (activeScan length (storePair s.resource a b z).value [a,b]).value.length ≤ 2 := by
    rw [activeScan_value]
    exact (List.length_filter_le _ _).trans_eq (by rfl)
  have ha := prependActive_cost (activeScan length (storePair s.resource a b z).value [a,b]).value tail
  unfold arrayUpdate
  rw [join_cost,join_cost,join_cost,join_cost]
  change _ + (3 + (_ + (_ + 1))) ≤ _
  simp only [List.length_cons,List.length_nil] at hr
  dsimp only
  omega

/-- A generated word-address array is traversed once to produce the loop's
index spine. Both generation and spine materialization have named prices. -/
noncomputable def addressRange (n : ℕ) : Run (List (Fin n)) :=
  let generated := arrayRun n (fun j => (⟨j,[.control]⟩ : Run (Fin n)))
  ⟨generated.value.data.toList,
    generated.trace ++ (List.ofFn (fun j : Fin n => [Operation.control,.storeCell j.val])).flatten ++ [.control]⟩

theorem addressRange_value (n : ℕ) : (addressRange n).value = List.finRange n := by
  have hArray : (arrayRun n (fun j => (⟨j,[Operation.control]⟩ : Run (Fin n)))).value = FixedArrayTable.ofFn id := by
    apply table_ext
    intro j
    rw [arrayRun_read,FixedArrayTable.read_ofFn]
    rfl
  simp only [addressRange,hArray,FixedArrayTable.ofFn,Array.toList_ofFn,List.ofFn_id]

theorem addressRange_cost (n : ℕ) : (addressRange n).cost ≤ 5 * n + 3 := by
  have hArray := arrayRun_bound n 1 (fun j => (⟨j,[Operation.control]⟩ : Run (Fin n))) (fun _ => by rfl)
  unfold addressRange
  change cost (_ ++ (List.ofFn _).flatten ++ [.control]) ≤ _
  rw [cost_append,cost_append,cost_flatten]
  simp only [List.map_ofFn,List.sum_ofFn,cost_cons,cost_nil,Operation.cost]
  change (arrayRun n _).cost + (∑ _j : Fin n, 2) + 1 ≤ _
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  omega

noncomputable def initialState {n : ℕ} (length resource : FixedArrayTable n ℝ) : Run (ArrayResourceState length.read) :=
  let cells : ResourceArray n := ⟨resource.data,resource.size⟩
  let indices := addressRange n
  let active := activeScan length cells indices.value
  let reference := ActiveResourceList.initial length.read cells.allocation
  have hActive : active.value = reference.active := by
    simp only [active,activeScan_value,indices,addressRange_value,reference,ActiveResourceList.initial]
  let produced : ArrayResourceState length.read :=
    ⟨cells,active.value,
      by rw [hActive]; exact reference.nodup,
      by rw [hActive]; exact reference.membership⟩
  join indices (join active ⟨produced,[.control,.control,.control]⟩)

theorem initialState_view {n : ℕ} (length resource : FixedArrayTable n ℝ) :
    (initialState length resource).value.view = ActiveResourceList.initial length.read resource.read := by
  apply ActiveResourceList.eq_of_fields
  · rfl
  · simp only [initialState,join_value,ArrayResourceState.view,activeScan_value,addressRange_value,ActiveResourceList.initial]
    rfl

theorem initialState_cost {n : ℕ} (length resource : FixedArrayTable n ℝ) :
    (initialState length resource).cost ≤ 13 * n + 7 := by
  have hi := addressRange_cost n
  have hs := activeScan_cost length (⟨resource.data,resource.size⟩ : ResourceArray n) (addressRange n).value
  unfold initialState
  rw [join_cost,join_cost]
  change _ + (_ + 3) ≤ _
  rw [addressRange_value]
  rw [addressRange_value] at hs
  simp only [List.length_finRange] at hs
  omega

noncomputable def sourceLoop {n : ℕ} {L : Allocation n} (length : FixedArrayTable n ℝ) (hL : length.read = L) :
    (C : ℕ) → ArrayResourceState L → (Fin C → ℝ) → Run (ArrayResourceState L)
  | 0, s, _ => ⟨s,[.control]⟩
  | C + 1, s, seed =>
    match he : s.active with
    | [] => ⟨s,[.control,.control,.control]⟩
    | [_] => ⟨s,[.control,.control,.control]⟩
    | a :: b :: tail =>
      let fields := pairValues length s.resource a b
      let u := uniform (seed 0)
      let compared := compareLe u.value fields.value.probability
      let z := if compared.value then fields.value.upper else fields.value.lower
      let next := arrayUpdate length hL s a b tail he z
      join (⟨(),[.control,.control,.control,.control]⟩ : Run Unit) (join fields (join u (join compared
        (join next (join (⟨(),[.control]⟩ : Run Unit) (sourceLoop length hL C next.value (Fin.tail seed)))))))

theorem sourceLoop_cost {n : ℕ} {L : Allocation n} (length : FixedArrayTable n ℝ) (hL : length.read = L)
    (C : ℕ) (s : ArrayResourceState L) (seed : Fin C → ℝ) :
    (sourceLoop length hL C s seed).cost ≤ 150 * C + 3 := by
  induction C generalizing s with
  | zero => simp [sourceLoop,Run.cost,Operation.cost]
  | succ C ih =>
    unfold sourceLoop
    split
    · change 3 ≤ _; omega
    · change 3 ≤ _; omega
    · rename_i a b tail he
      dsimp only
      rw [join_cost,join_cost,join_cost,join_cost,join_cost,join_cost]
      have hp := pairValues_cost length s.resource a b
      have hu : (uniform (seed 0)).cost = 1 := rfl
      have hc : (compareLe (uniform (seed 0)).value (pairValues length s.resource a b).value.probability).cost = 1 := rfl
      let z := if (compareLe (uniform (seed 0)).value (pairValues length s.resource a b).value.probability).value then
        (pairValues length s.resource a b).value.upper else (pairValues length s.resource a b).value.lower
      have hn := arrayUpdate_cost length hL s a b tail he z
      have hr := ih (arrayUpdate length hL s a b tail he z).value (Fin.tail seed)
      have hHead : (⟨(),[Operation.control,.control,.control,.control]⟩ : Run Unit).cost = 4 := rfl
      have hAdvance : (⟨(),[Operation.control]⟩ : Run Unit).cost = 1 := rfl
      rw [hu,hc,hHead,hAdvance]
      dsimp only [z] at hn hr
      omega

theorem sourceLoop_value {n : ℕ} {L : Allocation n} (length : FixedArrayTable n ℝ) (hL : length.read = L)
    (C : ℕ) (s : ArrayResourceState L) (seed : Fin C → ℝ) (fallback : Allocation n) :
    (sourceLoop length hL C s seed).value.resource.allocation =
      (roundActiveResources C s.view).realChoice.output C fallback seed := by
  induction C generalizing s with
  | zero => rfl
  | succ C ih =>
    cases s with
    | mk resource active nodup membership =>
      cases active with
      | nil => rfl
      | cons a rest =>
        cases rest with
        | nil => rfl
        | cons b tail =>
          let s : ArrayResourceState L := ⟨resource,a :: b :: tail,nodup,membership⟩
          let hp := s.view.selected_fractional (rfl : s.view.active = a :: b :: tail)
          let p := resourcePair L s.resource.allocation a b hp.1 hp.2
          have hI : Fractional length.read s.resource.allocation a := by rw [hL]; exact hp.1
          have hJ : Fractional length.read s.resource.allocation b := by rw [hL]; exact hp.2
          have hFields := pairValues_value length s.resource a b hI hJ
          dsimp only [resourcePair,RoundingPair.total,RoundingPair.lower,RoundingPair.upper,RoundingPair.probability] at hFields
          simp only [hL] at hFields
          change (pairValues length s.resource a b).value = ⟨p.total,p.lower,p.upper,p.probability⟩ at hFields
          change (sourceLoop length hL C (arrayUpdate length hL s a b tail rfl
            (if (compareLe (uniform (seed 0)).value (pairValues length s.resource a b).value.probability).value then
              (pairValues length s.resource a b).value.upper else (pairValues length s.resource a b).value.lower)).value
            (Fin.tail seed)).value.resource.allocation =
              (RealChoiceTree.fork p.probability ⟨p.probability_pos.le,p.probability_lt_one.le⟩
                (roundActiveResources C (s.view.update a b tail rfl p.upper)).realChoice
                (roundActiveResources C (s.view.update a b tail rfl p.lower)).realChoice).output (C + 1) fallback seed
          rw [RealChoiceTree.output_fork_succ,hFields]
          simp only [uniform,Operation.realValue,compareLe,RealThresholdChoice.sample]
          by_cases hCoin : seed 0 ≤ p.probability
          · simp [hCoin]
            rw [ih,arrayUpdate_value,ArrayResourceState.realUpdate_view]
          · simp [hCoin]
            rw [ih,arrayUpdate_value,ArrayResourceState.realUpdate_view]

noncomputable def source {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) : Run (FixedArrayTable n ℝ) :=
  let length := copyRow i.length
  let resources := copyRow i.initial
  let prepared := initialState length.value resources.value
  let sampled := sourceLoop length.value rfl (n - 1) prepared.value seed
  let output : FixedArrayTable n ℝ := ⟨sampled.value.resource.data,sampled.value.resource.size⟩
  join length (join resources (join prepared (join sampled ⟨output,[.control]⟩)))

theorem source_value {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    (source i seed).value.read = i.realPhase seed := by
  unfold source
  simp only [join_value]
  change (sourceLoop (copyRow i.length).value rfl (n - 1)
    (initialState (copyRow i.length).value (copyRow i.initial).value).value seed).value.resource.allocation = _
  rw [sourceLoop_value _ _ _ _ _ i.initial,initialState_view]
  rw [copyRow_read i.length,copyRow_read i.initial]
  rw [i.realPhase_refines]
  rfl

theorem source_cost {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    (source i seed).cost ≤ 169 * n + 25 := by
  have hp := initialState_cost (copyRow i.length).value (copyRow i.initial).value
  have hs := sourceLoop_cost (copyRow i.length).value rfl (n - 1)
    (initialState (copyRow i.length).value (copyRow i.initial).value).value seed
  unfold source
  rw [join_cost,join_cost,join_cost,join_cost]
  simp only [copyRow_cost]
  change (3 * n + 2) + ((3 * n + 2) + (_ + (_ + 1))) ≤ _
  omega

theorem source_valid {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    i.Valid (source i seed).value.read := by
  rw [source_value]
  exact i.realPhase_valid seed

theorem source_law {n : ℕ} (i : LottoResourceSystem n) :
    Measure.map (fun seed => (source i seed).value.read)
      (RealUniformInputs.law (n - 1) : Measure (Fin (n - 1) → ℝ)) =
        (i.tree.realChoice.idealLaw : Measure (Allocation n)) := by
  have h : (fun seed => (source i seed).value.read) = i.realPhase := funext (source_value i)
  rw [h]
  exact i.realPhase_law

theorem source_array {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    (source i seed).value = FixedArrayTable.ofFn (i.realPhase seed) := by
  apply table_ext
  intro j
  rw [FixedArrayTable.read_ofFn]
  exact congrFun (source_value i seed) j

theorem source_measurable {n : ℕ} (i : LottoResourceSystem n) :
    Measurable (fun seed => (source i seed).value.read) := by
  have h : (fun seed => (source i seed).value.read) = i.realPhase := funext (source_value i)
  rw [h]
  exact i.realPhase_measurable

theorem source_resource_contract {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    InBox i.length (source i seed).value.read ∧
      (∑ j, (source i seed).value.read j) = 2 * i.B ∧
        (fractionalSet i.length (source i seed).value.read).card ≤ 1 := source_valid i seed

/-- Copy incoming stored cells once into the private mutable resource region.
The iteration count comes from the actual incoming array header. -/
noncomputable def copyStored {n : ℕ} (input : FixedArrayTable n ℝ) : Run (FixedArrayTable n ℝ) :=
  let copied := arrayRun input.data.size (fun j => loadReal input (j.cast input.size))
  ⟨⟨copied.value.data,copied.value.size.trans input.size⟩,copied.trace⟩

theorem copyStored_value {n : ℕ} (input : FixedArrayTable n ℝ) :
    (copyStored input).value.read = input.read := by
  funext j
  unfold copyStored
  change (arrayRun input.data.size (fun k => loadReal input (k.cast input.size))).value.read
    (j.cast input.size.symm) = input.read j
  rw [arrayRun_read]
  change input.read ((j.cast input.size.symm).cast input.size) = input.read j
  apply congrArg input.read
  apply Fin.ext
  rfl

theorem copyStored_cost {n : ℕ} (input : FixedArrayTable n ℝ) :
    (copyStored input).cost ≤ 3 * n + 2 := by
  have h := arrayRun_bound input.data.size 1
    (fun j => loadReal input (j.cast input.size)) (fun _ => by rfl)
  change (arrayRun input.data.size _).cost ≤ _
  have hb : 2 + input.data.size * (1 + 2) ≤ 3 * n + 2 := by rw [input.size]; omega
  exact h.trans hb

/-- The cached source executes from the stored arrays directly. Its system
parameter is only a legality/readback certificate; no field of it is used to
produce an operand. The private resource copy preserves the prepared cache. -/
noncomputable def sourceStored {n : ℕ} (lengths initial : FixedArrayTable n ℝ)
    (seed : Fin (n - 1) → ℝ) : Run (FixedArrayTable n ℝ) :=
  let copied := copyStored initial
  let prepared := initialState lengths copied.value
  let count := lengths.data.size - 1
  let inputs : Fin count → ℝ := fun j => seed (j.cast (by dsimp only [count]; rw [lengths.size]))
  let sampled := sourceLoop lengths rfl count prepared.value inputs
  let output : FixedArrayTable n ℝ := ⟨sampled.value.resource.data,sampled.value.resource.size⟩
  join copied (join prepared (join sampled ⟨output,[.control,.control]⟩))

theorem sourceStored_value {n : ℕ} (i : LottoResourceSystem n)
    (lengths initial : FixedArrayTable n ℝ) (hL : lengths.read = i.length)
    (hI : initial.read = i.initial) (seed : Fin (n - 1) → ℝ) :
    (sourceStored lengths initial seed).value.read = i.realPhase seed := by
  cases lengths with
  | mk data size =>
    cases size
    unfold sourceStored
    simp only [join_value]
    change (sourceLoop (⟨data,rfl⟩ : FixedArrayTable data.size ℝ) rfl (data.size - 1)
      (initialState ⟨data,rfl⟩ (copyStored initial).value).value seed).value.resource.allocation = _
    rw [sourceLoop_value _ _ _ _ _ i.initial,initialState_view,copyStored_value,hL,hI]
    rw [i.realPhase_refines]
    rfl

theorem sourceStored_cost {n : ℕ} (lengths initial : FixedArrayTable n ℝ)
    (seed : Fin (n - 1) → ℝ) :
    (sourceStored lengths initial seed).cost ≤ 166 * n + 20 := by
  have hc := copyStored_cost initial
  have hp := initialState_cost lengths (copyStored initial).value
  have hs := sourceLoop_cost lengths rfl (lengths.data.size - 1)
    (initialState lengths (copyStored initial).value).value
    (fun j => seed (j.cast (by rw [lengths.size])))
  have hSize := lengths.size
  unfold sourceStored
  rw [join_cost,join_cost,join_cost]
  change _ + (_ + (_ + 2)) ≤ _
  omega

theorem sourceStored_valid {n : ℕ} (i : LottoResourceSystem n)
    (lengths initial : FixedArrayTable n ℝ) (hL : lengths.read = i.length)
    (hI : initial.read = i.initial) (seed : Fin (n - 1) → ℝ) :
    i.Valid (sourceStored lengths initial seed).value.read := by
  rw [sourceStored_value i lengths initial hL hI]
  exact i.realPhase_valid seed

theorem sourceStored_law {n : ℕ} (i : LottoResourceSystem n)
    (lengths initial : FixedArrayTable n ℝ) (hL : lengths.read = i.length)
    (hI : initial.read = i.initial) :
    Measure.map (fun seed => (sourceStored lengths initial seed).value.read)
      (RealUniformInputs.law (n - 1) : Measure (Fin (n - 1) → ℝ)) =
        (i.tree.realChoice.idealLaw : Measure (Allocation n)) := by
  have h : (fun seed => (sourceStored lengths initial seed).value.read) = i.realPhase :=
    funext (sourceStored_value i lengths initial hL hI)
  rw [h]
  exact i.realPhase_law

end Blotto.RealPRGResourceExecution
