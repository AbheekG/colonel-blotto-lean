import Blotto.BinaryPRGResourceLifetime
import Blotto.BinaryCachedTerminalWork

/-! Data-only terminal classification and next-fit packing carry ghost source
allocation traces. All actual comparison/addition scratch, reversed members,
source records and recursive activations are retained conservatively. Exact
old classification and packed stored words are preserved. Source lattice/box
promises derive reached widths; input words and member indices remain shared.
Array conversion, route construction and later factories/draws are separate
joins; native allocator/layout/GC and scalar-record realizations are not claimed.
-/
set_option autoImplicit false
namespace Blotto.BinaryTerminalPrefixLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryRationalOpcode BinaryPRGResourceWork BinaryPRGTerminalWork
open BinaryTerminalClassificationWork BinaryGreedyPackingWork BinaryPRGPreparationWork

structure Classification (n : ℕ) where
  uniforms : List (Fin n)
  pivot : Option (Fin n)

def classificationWithTrace {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    List (Fin n) → Classification n × Trace
  | [] => (⟨[],none⟩,[.frames 1,.arrayAllocation 8])
  | j :: rest =>
      let resource := input.resource.read j
      let length := input.length.read j
      let upward := BinaryRationalOpcodeAllocation.lessEqualWithAllocation resource length
      let downward := BinaryRationalOpcodeAllocation.lessEqualWithAllocation length resource
      let nonpositive := BinaryRationalOpcodeAllocation.lessEqualWithAllocation resource zero
      let later := classificationWithTrace input rest
      (⟨if upward.1 && downward.1 then j :: later.1.uniforms else later.1.uniforms,
        if (!nonpositive.1) && (!downward.1) then some j else later.1.pivot⟩,
        [.frames 1,.arrayAllocation 8,.listAllocation 1,
          .listAllocation (BinaryRationalOpcodeAllocation.lessEqualStorage resource length),
          .listAllocation (BinaryRationalOpcodeAllocation.lessEqualStorage length resource),
          .listAllocation (BinaryRationalOpcodeAllocation.lessEqualStorage resource zero)] ++ under 1 later.2)

theorem classificationWithTrace_erases {n : ℕ} (input : BinaryTerminalGrouping.Input n) (items : List (Fin n)) :
    (classificationWithTrace input items).1.uniforms = (classifyAux input items).uniforms ∧
    (classificationWithTrace input items).1.pivot = (classifyAux input items).pivot := by
  induction items with
  | nil => exact ⟨rfl,rfl⟩
  | cons j rest ih =>
      simp only [classificationWithTrace,classifyAux,BinaryRationalOpcodeAllocation.lessEqualWithAllocation_state,ih]
      exact ⟨trivial,trivial⟩

def classificationWithTraceAndWork {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    List (Fin n) → (Classification n × Trace) × ℕ
  | [] => ((⟨[],none⟩,[.frames 1,.arrayAllocation 8]),0)
  | j :: rest =>
      let resource := input.resource.read j
      let length := input.length.read j
      let upward := BinaryRationalOpcodeAllocation.lessEqualWithAllocation resource length
      let downward := BinaryRationalOpcodeAllocation.lessEqualWithAllocation length resource
      let nonpositive := BinaryRationalOpcodeAllocation.lessEqualWithAllocation resource zero
      let later := classificationWithTraceAndWork input rest
      ((⟨if upward.1 && downward.1 then j :: later.1.1.uniforms else later.1.1.uniforms,
        if (!nonpositive.1) && (!downward.1) then some j else later.1.1.pivot⟩,
        [.frames 1,.arrayAllocation 8,.listAllocation 1,
          .listAllocation (BinaryRationalOpcodeAllocation.lessEqualStorage resource length),
          .listAllocation (BinaryRationalOpcodeAllocation.lessEqualStorage length resource),
          .listAllocation (BinaryRationalOpcodeAllocation.lessEqualStorage resource zero)] ++ under 1 later.1.2),
        BinaryRationalArithmetic.lessEqualWork resource length +
          BinaryRationalArithmetic.lessEqualWork length resource +
          BinaryRationalArithmetic.lessEqualWork resource zero + later.2)

theorem classificationWithTraceAndWork_erases {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) (items : List (Fin n)) :
    (classificationWithTraceAndWork input items).1 = classificationWithTrace input items := by
  induction items with
  | nil => rfl
  | cons j rest ih =>
      simp only [classificationWithTraceAndWork,classificationWithTrace,ih]

theorem classificationWithTraceAndWork_charge {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) (items : List (Fin n)) :
    (classificationWithTraceAndWork input items).2 =
      (BinaryTerminalClassificationWork.classifyAux input items).booleanWork := by
  induction items with
  | nil => rfl
  | cons j rest ih =>
      simp only [classificationWithTraceAndWork,
        BinaryTerminalClassificationWork.classifyAux,ih]

theorem classificationWithTrace_bounds {n : ℕ} (input : BinaryTerminalGrouping.Input n) (items : List (Fin n))
    (W : ℕ) (hW : 1  ≤  W) (hL : ∀ j,width (input.length.read j)  ≤  W) (hR : ∀ j,width (input.resource.read j)  ≤  W) :
    listCells (classificationWithTrace input items).2+arraySlots (classificationWithTrace input items).2   ≤  
      items.length*(7500*(W+1)^3+9)+8 ∧ framePeak (classificationWithTrace input items).2  ≤  items.length+1 := by
  induction items with
  | nil => simp [classificationWithTrace,listCells,arraySlots,framePeak]
  | cons j rest ih =>
      have hA := (BinaryRationalOpcodeAllocation.lessEqualStorage_bound (input.resource.read j) (input.length.read j)).trans
        (Nat.mul_le_mul_left 2500 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le (hR j) (hL j)) 1) 3))
      have hB := (BinaryRationalOpcodeAllocation.lessEqualStorage_bound (input.length.read j) (input.resource.read j)).trans
        (Nat.mul_le_mul_left 2500 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le (hL j) (hR j)) 1) 3))
      have hC := (BinaryRationalOpcodeAllocation.lessEqualStorage_bound (input.resource.read j) zero).trans
        (Nat.mul_le_mul_left 2500 (Nat.pow_le_pow_left (Nat.add_le_add_right
          (max_le (hR j) (show width zero  ≤  W from hW)) 1) 3))
      have hu := framePeak_under 1 (classificationWithTrace input rest).2
      simp only [classificationWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
        listCells_under,arraySlots_under,List.length_cons]
      exact ⟨by nlinarith only [hA,hB,hC,ih.1],by omega⟩

-- Every attempted packing sum is retained once. Both closed-group reversals
-- and the final reversal are reserved; reserve a full current prefix even on
-- a fitting branch, so no ownership or reclamation assumption is hidden.
def packAuxWithTrace {α : Type*} (length : α→SignedWord) (budget : SignedWord) :
    List α → SignedWord → List α → List (List α×SignedWord) × Trace
  | current,total,[] => ([(current.reverse,total)],[.frames (current.length+8),
      .listAllocation (current.length+3),.arrayAllocation 8])
  | current,total,item::rest =>
      let added := BinaryRationalOpcodeAllocation.applyWithAllocation .add total (length item)
      let comparison := BinaryRationalOpcodeAllocation.lessEqualWithAllocation added.1 budget
      let localTrace := [.frames (current.length+8),.arrayAllocation 8,.listAllocation (current.length+4),
        .listAllocation (BinaryRationalOpcodeAllocation.opcodeStorage .add total (length item)),
        .listAllocation (BinaryRationalOpcodeAllocation.lessEqualStorage added.1 budget)]
      if comparison.1 then
        let later := packAuxWithTrace length budget (item::current) added.1 rest
        (later.1,localTrace ++ under 1 later.2)
      else
        let later := packAuxWithTrace length budget [item] (length item) rest
        ((current.reverse,total)::later.1,localTrace ++ under 1 later.2)

theorem packAuxWithTrace_erases {α : Type*} (length : α→SignedWord) (budget : SignedWord)
    (current : List α) (total : SignedWord) (rest : List α) :
    (packAuxWithTrace length budget current total rest).1 = BinaryGreedyPacking.packAux length budget current total rest := by
  induction rest generalizing current total with
  | nil => rfl
  | cons item rest ih =>
      simp only [packAuxWithTrace,BinaryGreedyPacking.packAux,BinaryRationalOpcodeAllocation.applyWithAllocation_state,
        BinaryRationalOpcodeAllocation.lessEqualWithAllocation_state]
      split <;> simp only [ih]

def packAuxWithTraceAndWork {α : Type*} (length : α→SignedWord) (budget : SignedWord) :
    List α → SignedWord → List α → (List (List α×SignedWord) × Trace) × ℕ
  | current,total,[] =>
      (([(current.reverse,total)],[.frames (current.length+8),
        .listAllocation (current.length+3),.arrayAllocation 8]),0)
  | current,total,item::rest =>
      let added := BinaryRationalOpcodeAllocation.applyWithAllocation .add total (length item)
      let comparison := BinaryRationalOpcodeAllocation.lessEqualWithAllocation added.1 budget
      let localTrace := [.frames (current.length+8),.arrayAllocation 8,.listAllocation (current.length+4),
        .listAllocation (BinaryRationalOpcodeAllocation.opcodeStorage .add total (length item)),
        .listAllocation (BinaryRationalOpcodeAllocation.lessEqualStorage added.1 budget)]
      let localWork := (applyWithWork .add total (length item)).2 +
        BinaryRationalArithmetic.lessEqualWork added.1 budget
      if comparison.1 then
        let later := packAuxWithTraceAndWork length budget (item::current) added.1 rest
        ((later.1.1,localTrace ++ under 1 later.1.2),localWork + later.2)
      else
        let later := packAuxWithTraceAndWork length budget [item] (length item) rest
        (((current.reverse,total)::later.1.1,localTrace ++ under 1 later.1.2),
          localWork + later.2)

theorem packAuxWithTraceAndWork_erases {α : Type*} (length : α→SignedWord)
    (budget : SignedWord) (current : List α) (total : SignedWord) (rest : List α) :
    (packAuxWithTraceAndWork length budget current total rest).1 =
      packAuxWithTrace length budget current total rest := by
  induction rest generalizing current total with
  | nil => rfl
  | cons item rest ih =>
      simp only [packAuxWithTraceAndWork,packAuxWithTrace]
      split <;> simp only [ih]

theorem packAuxWithTraceAndWork_charge {α : Type*} (length : α→SignedWord)
    (budget : SignedWord) (current : List α) (total : SignedWord) (rest : List α) :
    (packAuxWithTraceAndWork length budget current total rest).2 =
      (BinaryGreedyPackingWork.packAux length budget current total rest).2 := by
  induction rest generalizing current total with
  | nil => rfl
  | cons item rest ih =>
      simp only [packAuxWithTraceAndWork,BinaryGreedyPackingWork.packAux,
        BinaryRationalOpcodeAllocation.applyWithAllocation_state,
        BinaryRationalOpcodeAllocation.lessEqualWithAllocation_state,applyWithWork_state]
      split <;> simp_all

def packingStepBound (W : ℕ) : ℕ := 2000000*(W+2)^4+2500*(3*W+2)^3

theorem packingStepBound_mono {a b : ℕ} (h : a ≤ b) : packingStepBound a ≤ packingStepBound b := by
  unfold packingStepBound
  gcongr

theorem packingStep_bound (total leaf budget : SignedWord) (W : ℕ)
    (hT : width total  ≤  W) (hL : width leaf  ≤  W) (hB : width budget  ≤  W) :
    BinaryRationalOpcodeAllocation.opcodeStorage .add total leaf+
      BinaryRationalOpcodeAllocation.lessEqualStorage (apply .add total leaf) budget  ≤  packingStepBound W := by
  have hAdd := (BinaryRationalOpcodeAllocation.opcodeStorage_bound .add total leaf).trans
    (Nat.mul_le_mul_left 2000000 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le hT hL) 2) 4))
  have hNext : width (apply .add total leaf)  ≤  3*W+1 :=
    (apply_stored_width .add total leaf).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (max_le hT hL)) 1)
  have hCompare := (BinaryRationalOpcodeAllocation.lessEqualStorage_bound (apply .add total leaf) budget).trans
    (Nat.mul_le_mul_left 2500 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le hNext (hB.trans (by omega))) 1) 3))
  unfold packingStepBound
  nlinarith only [hAdd,hCompare]

set_option maxHeartbeats 1000000 in
theorem packAuxWithTrace_bounds {α : Type*} (length : α→SignedWord) (budget : SignedWord)
    (D : ℕ) (hD : 0<D) (hB : CanonicalWord budget) (hBL : OnRationalLattice D (value budget))
    (hBox : 0  ≤  value budget ∧ value budget  ≤  1) (hLength : ∀ item,GoodTotal D budget (length item))
    (current : List α) (total : SignedWord) (rest : List α) (hTotal : GoodTotal D budget total) :
    listCells (packAuxWithTrace length budget current total rest).2+
      arraySlots (packAuxWithTrace length budget current total rest).2   ≤  
      rest.length*packingStepBound (1+2*binaryWordWidth D)+
        (rest.length+1)*(current.length+rest.length+12) ∧
    framePeak (packAuxWithTrace length budget current total rest).2   ≤   current.length+2*rest.length+8 := by
  induction rest generalizing current total with
  | nil => simp [packAuxWithTrace,listCells,arraySlots,framePeak]
  | cons item rest ih =>
      have hBudget : width budget  ≤  1+2*binaryWordWidth D :=
        hB.2.trans (rationalWordWidth_lattice_bound hD hBL hBox)
      have hStep := packingStep_bound total (length item) budget (1+2*binaryWordWidth D)
        (goodTotal_width D hD budget total hBox.2 hTotal)
        (goodTotal_width D hD budget (length item) hBox.2 (hLength item)) hBudget
      unfold packAuxWithTrace
      simp only [BinaryRationalOpcodeAllocation.applyWithAllocation_state,BinaryRationalOpcodeAllocation.lessEqualWithAllocation_state]
      split
      · rename_i hFit
        have hNext : GoodTotal D budget (apply .add total (length item)) := by
          have hh := next_good D budget total (length item) hB hTotal (hLength item)
            (show BinaryRationalArithmetic.lessEqual (applyWithWork .add total (length item)).1 budget=true by
              simpa only [applyWithWork_state] using hFit)
          simpa only [applyWithWork_state] using hh
        have hRest := ih (item::current) (apply .add total (length item)) hNext
        have hFrame := framePeak_under 1 (packAuxWithTrace length budget (item::current) (apply .add total (length item)) rest).2
        simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,
          arraySlots_under,List.length_cons] at hRest ⊢
        exact ⟨by nlinarith only [hStep,hRest.1],by omega⟩
      · have hRest := ih [item] (length item) (hLength item)
        have hFrame := framePeak_under 1 (packAuxWithTrace length budget [item] (length item) rest).2
        simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,
          arraySlots_under,List.length_cons,List.length_nil] at hRest ⊢
        exact ⟨by nlinarith only [hStep,hRest.1],by omega⟩

def packingWithTrace {α : Type*} (length : α→SignedWord) (budget : SignedWord) : List α → List (List α×SignedWord) × Trace
  | [] => ([],[.frames 1,.arrayAllocation 8])
  | item::rest =>
      let later := packAuxWithTrace length budget [item] (length item) rest
      (later.1,[.frames 1,.listAllocation 1,.arrayAllocation 8] ++ under 1 later.2)

theorem packingWithTrace_erases {α : Type*} (length : α→SignedWord) (budget : SignedWord) (items : List α) :
    (packingWithTrace length budget items).1 = BinaryGreedyPacking.packedGroups length budget items := by
  cases items with
  | nil => rfl
  | cons item rest => exact packAuxWithTrace_erases length budget [item] (length item) rest

def packingWithTraceAndWork {α : Type*} (length : α→SignedWord) (budget : SignedWord) :
    List α → (List (List α×SignedWord) × Trace) × ℕ
  | [] => (([],[.frames 1,.arrayAllocation 8]),0)
  | item::rest =>
      let later := packAuxWithTraceAndWork length budget [item] (length item) rest
      ((later.1.1,[.frames 1,.listAllocation 1,.arrayAllocation 8] ++ under 1 later.1.2),later.2)

theorem packingWithTraceAndWork_erases {α : Type*} (length : α→SignedWord)
    (budget : SignedWord) (items : List α) :
    (packingWithTraceAndWork length budget items).1 = packingWithTrace length budget items := by
  cases items with
  | nil => rfl
  | cons item rest =>
      simp only [packingWithTraceAndWork,packingWithTrace,packAuxWithTraceAndWork_erases]

theorem packingWithTraceAndWork_charge {α : Type*} (length : α→SignedWord)
    (budget : SignedWord) (items : List α) :
    (packingWithTraceAndWork length budget items).2 =
      (BinaryGreedyPackingWork.pack length budget items).2 := by
  cases items with
  | nil => rfl
  | cons item rest =>
      exact packAuxWithTraceAndWork_charge length budget [item] (length item) rest

theorem packingWithTrace_bounds {α : Type*} (length : α→SignedWord) (budget : SignedWord)
    (D : ℕ) (hD : 0<D) (hB : CanonicalWord budget) (hBL : OnRationalLattice D (value budget))
    (hBox : 0  ≤  value budget ∧ value budget  ≤  1) (hLength : ∀ item,GoodTotal D budget (length item)) (items : List α) :
    listCells (packingWithTrace length budget items).2+arraySlots (packingWithTrace length budget items).2   ≤  
      items.length*packingStepBound (1+2*binaryWordWidth D)+items.length*(items.length+12)+9 ∧
    framePeak (packingWithTrace length budget items).2  ≤  2*items.length+8 := by
  cases items with
  | nil => simp [packingWithTrace,listCells,arraySlots,framePeak]
  | cons item rest =>
      have h := packAuxWithTrace_bounds length budget D hD hB hBL hBox hLength [item] (length item) rest (hLength item)
      have hf := framePeak_under 1 (packAuxWithTrace length budget [item] (length item) rest).2
      simp only [packingWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
        listCells_under,arraySlots_under,List.length_cons,List.length_nil] at h ⊢
      exact ⟨by nlinarith only [h.1],by omega⟩


def prefixWithTraceAndWork {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    (Classification n × (List (List (Fin n)×SignedWord) × Trace)) × ℕ :=
  let classified := classificationWithTraceAndWork input (List.finRange n)
  let packed := packingWithTraceAndWork input.length.read input.budget classified.1.1.uniforms
  ((classified.1.1,(packed.1.1,[.frames (n+8),.listAllocation n,.arrayAllocation 8] ++
    under 2 classified.1.2 ++ under 2 packed.1.2)),classified.2)

def prefixWithTraceAndArithmeticWork {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    (Classification n × (List (List (Fin n)×SignedWord) × Trace)) × ℕ :=
  let classified := classificationWithTraceAndWork input (List.finRange n)
  let packed := packingWithTraceAndWork input.length.read input.budget classified.1.1.uniforms
  ((classified.1.1,(packed.1.1,[.frames (n+8),.listAllocation n,.arrayAllocation 8] ++
    under 2 classified.1.2 ++ under 2 packed.1.2)),classified.2+packed.2)

def prefixWithTrace {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    Classification n × (List (List (Fin n)×SignedWord) × Trace) :=
  (prefixWithTraceAndArithmeticWork input).1

theorem prefixWithTraceAndArithmeticWork_erases {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (prefixWithTraceAndArithmeticWork input).1 = prefixWithTrace input := rfl

theorem prefixWithTraceAndWork_charge {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    (prefixWithTraceAndWork input).2 = (classifyAndPack input).1.booleanWork := by
  simp only [prefixWithTraceAndWork,classifyAndPack,classify,
    classificationWithTraceAndWork_charge]

def prefixWithTraceAndPackingWork {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    (Classification n × (List (List (Fin n)×SignedWord) × Trace)) × ℕ :=
  let classified := classificationWithTraceAndWork input (List.finRange n)
  let packed := packingWithTraceAndWork input.length.read input.budget classified.1.1.uniforms
  ((classified.1.1,(packed.1.1,[.frames (n+8),.listAllocation n,.arrayAllocation 8] ++
    under 2 classified.1.2 ++ under 2 packed.1.2)),packed.2)

theorem prefixWithTraceAndPackingWork_erases {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (prefixWithTraceAndPackingWork input).1 = prefixWithTrace input := rfl

theorem prefixWithTraceAndPackingWork_charge {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (prefixWithTraceAndPackingWork input).2 =
      (BinaryGreedyPackingWork.pack input.length.read input.budget
        (BinaryTerminalGrouping.uniformItems input)).2 := by
  unfold prefixWithTraceAndPackingWork
  dsimp only
  rw [packingWithTraceAndWork_charge,classificationWithTraceAndWork_erases,
    (classificationWithTrace_erases input (List.finRange n)).1]
  exact congrArg (fun items => (BinaryGreedyPackingWork.pack input.length.read input.budget items).2)
    (BinaryTerminalClassificationWork.classify_state input).1

theorem prefixWithTraceAndPackingWork_bound {n : ℕ}
    (request : BinaryPRGRequest.Request n) (rich : Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length) :
    (prefixWithTraceAndPackingWork (terminalInput request rich state)).2 ≤
      160000*(n-1)*(request.source.originalInputWordWidth+2)^3 := by
  rw [prefixWithTraceAndPackingWork_charge]
  exact BinaryPRGTerminalWork.packing_boolean_bound request rich state

theorem prefixWithTraceAndArithmeticWork_charge {n : ℕ}
    (input : BinaryTerminalGrouping.Input n) :
    (prefixWithTraceAndArithmeticWork input).2 =
      (classifyAndPack input).1.booleanWork +
        (BinaryGreedyPackingWork.pack input.length.read input.budget
          (BinaryTerminalGrouping.uniformItems input)).2 := by
  have hClass := prefixWithTraceAndWork_charge input
  have hPack := prefixWithTraceAndPackingWork_charge input
  simpa only [prefixWithTraceAndArithmeticWork,prefixWithTraceAndWork,
    prefixWithTraceAndPackingWork] using
      congrArg₂ (fun first second : ℕ => first + second) hClass hPack

theorem prefixWithTraceAndArithmeticWork_reached_bound {n : ℕ}
    (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N→Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1=some state) :
    (prefixWithTraceAndArithmeticWork (terminalInput request rich state)).2 ≤
      166000*n*(request.source.originalInputWordWidth+2)^3 := by
  rw [prefixWithTraceAndArithmeticWork_charge]
  have hOld := BinaryTerminalClassificationWork.reached_classifyAndPack_boolean_bound
    request rich N bits state h
  unfold BinaryTerminalClassificationWork.classifyAndPack at hOld
  dsimp only at hOld
  rw [(BinaryTerminalClassificationWork.classify_state
    (terminalInput request rich state)).1] at hOld
  exact hOld

theorem prefixWithTraceAndWork_reached_bound {n : ℕ}
    (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N→Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1=some state) :
    (prefixWithTraceAndWork (terminalInput request rich state)).2 ≤
      6000*n*(request.source.originalInputWordWidth+2)^2 := by
  rw [prefixWithTraceAndWork_charge]
  exact BinaryTerminalClassificationWork.reached_classification_boolean_bound
    request rich N bits state h

theorem prefixWithTrace_erases {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    (prefixWithTrace input).1.uniforms = (classifyAndPack input).1.uniforms ∧
    (prefixWithTrace input).1.pivot = (classifyAndPack input).1.pivot ∧
    (prefixWithTrace input).2.1 = (classifyAndPack input).2.1 := by
  have hc := classificationWithTrace_erases input (List.finRange n)
  unfold prefixWithTrace prefixWithTraceAndArithmeticWork classifyAndPack classify
  simp only [classificationWithTraceAndWork_erases,packingWithTraceAndWork_erases]
  refine ⟨hc.1,hc.2,?_⟩
  rw [packingWithTrace_erases,hc.1,pack_state]

noncomputable def prefixBound {n : ℕ} (request : BinaryPRGRequest.Request n) : ℕ :=
  n*(7500*(4+2*request.source.originalInputWordWidth)^3+9)+8+
    n*packingStepBound (3+2*request.source.originalInputWordWidth)+n*(n+12)+9+n+8

theorem reached_prefix_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N→Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1=some state) :
    listCells (prefixWithTrace (terminalInput request rich state)).2.2+
      arraySlots (prefixWithTrace (terminalInput request rich state)).2.2  ≤  prefixBound request ∧
    framePeak (prefixWithTrace (terminalInput request rich state)).2.2  ≤  2*n+10 := by
  let input := terminalInput request rich state
  let classified := classificationWithTrace input (List.finRange n)
  have hc := classificationWithTrace_bounds input (List.finRange n)
    (1+2*binaryWordWidth request.source.normalizedInput.latticeDenominator) (by omega)
    (terminal_length_width request rich state) (terminal_resource_width request rich N bits state h)
  have he := classificationWithTrace_erases input (List.finRange n)
  have hUniforms : classified.1.uniforms.length  ≤  n := by
    change (classificationWithTrace input (List.finRange n)).1.uniforms.length  ≤  n
    rw [he.1,classifyAux_uniforms]
    simpa only [List.length_finRange] using List.length_filter_le (BinaryTerminalGrouping.uniform input) (List.finRange n)
  have hp := packingWithTrace_bounds input.length.read input.budget request.source.normalizedInput.latticeDenominator
    request.source.normalizedInput.latticeDenominator_pos (terminal_canonical request rich state).1
    (budget_lattice request rich) (budget_box request rich) (length_good request rich) classified.1.uniforms
  have hCFrames := framePeak_under 2 classified.2
  have hPFrames := framePeak_under 2 (packingWithTrace input.length.read input.budget classified.1.uniforms).2
  simp only [List.length_finRange] at hc
  have hWidth : 1+2*binaryWordWidth request.source.normalizedInput.latticeDenominator  ≤ 
      3+2*request.source.originalInputWordWidth := by
    have hd := request.source.normalized_lattice_wordWidth_original
    omega
  have hClassification : n*(7500*(1+2*binaryWordWidth request.source.normalizedInput.latticeDenominator+1)^3+9)+8  ≤ 
      n*(7500*(4+2*request.source.originalInputWordWidth)^3+9)+8 := by
    have hPow := Nat.pow_le_pow_left
      (show 1+2*binaryWordWidth request.source.normalizedInput.latticeDenominator+1 ≤ 4+2*request.source.originalInputWordWidth by omega) 3
    exact Nat.add_le_add_right (Nat.mul_le_mul_left n (Nat.add_le_add_right (Nat.mul_le_mul_left 7500 hPow) 9)) 8
  have hPacking : classified.1.uniforms.length*packingStepBound (1+2*binaryWordWidth request.source.normalizedInput.latticeDenominator)+
      classified.1.uniforms.length*(classified.1.uniforms.length+12)+9  ≤ 
      n*packingStepBound (3+2*request.source.originalInputWordWidth)+n*(n+12)+9 := by
    exact Nat.add_le_add_right (Nat.add_le_add
      (Nat.mul_le_mul hUniforms (packingStepBound_mono hWidth))
      (Nat.mul_le_mul hUniforms (Nat.add_le_add_right hUniforms 12))) 9
  have hCBound := hc.1.trans hClassification
  have hPBound := hp.1.trans hPacking
  unfold prefixWithTrace prefixWithTraceAndArithmeticWork prefixBound
  simp only [classificationWithTraceAndWork_erases,packingWithTraceAndWork_erases]
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
  dsimp only [classified,input] at hCBound hPBound hc hp hUniforms hCFrames hPFrames
  exact ⟨by nlinarith only [hCBound,hPBound],by omega⟩

theorem reached_prefix_all_prefix {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N→Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1=some state) (borrowedCells steps : ℕ) :
    retainedHeap borrowedCells (prefixWithTrace (terminalInput request rich state)).2.2 steps  ≤  borrowedCells+prefixBound request := by
  have hb := (reached_prefix_bound request rich N bits state h).1
  have hl := listCells_take_le (prefixWithTrace (terminalInput request rich state)).2.2 steps
  have ha := arraySlots_take_le (prefixWithTrace (terminalInput request rich state)).2.2 steps
  unfold retainedHeap
  omega

end Blotto.BinaryTerminalPrefixLifetime
