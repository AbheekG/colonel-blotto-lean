import Blotto.BinaryCachePrefixPlan
import Blotto.BinaryCubicOpcodeMeasured

/-! Classification and next-fit packing consume actual comparison and cubic
opcode records. The prior complete plan and source price remain exact, while
the reached arithmetic work is returned separately and paid by four times that
price. Index enumeration, list control and native metadata retain their scope. -/
namespace Blotto.BinaryCacheArithmeticPrefix
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryTracePlanMeasured
open BinaryTerminalPrefixLifetime
set_option autoImplicit false
set_option maxHeartbeats 3000000

def classificationAt {n : ℕ} (input : BinaryTerminalGrouping.Input n) :
    List (Fin n) → ℕ → ((Classification n × Plan) × ℕ) × ℕ
  | [],depth => (((⟨[],none⟩,.block [.frames (depth+1),.arrayAllocation 8]),0),0)
  | j::rest,depth =>
      let resource := input.resource.read j
      let length := input.length.read j
      let upward := BinaryRationalComparisonMeasured.compare resource length
      let downward := BinaryRationalComparisonMeasured.compare length resource
      let nonpositive := BinaryRationalComparisonMeasured.compare resource BinaryRationalOpcode.zero
      let returned := classificationAt input rest (depth+1)
      let later := returned.1
      let localWork := upward.work+downward.work+nonpositive.work
      (((⟨if upward.data && downward.data then j::later.1.1.uniforms else later.1.1.uniforms,
        if (!nonpositive.data) && (!downward.data) then some j else later.1.1.pivot⟩,
        .join (.block [.frames (depth+1),.arrayAllocation 8,.listAllocation 1,
          .listAllocation upward.storage,.listAllocation downward.storage,.listAllocation nonpositive.storage])
          later.1.2),localWork+later.2),localWork+returned.2)

theorem classification_compat {n : ℕ} (input : BinaryTerminalGrouping.Input n) (items : List (Fin n)) (depth : ℕ) :
    (classificationAt input items depth).1 = BinaryCachePrefixPlan.classificationAt input items depth := by
  induction items generalizing depth with
  | nil => rfl
  | cons j rest ih =>
      simp only [classificationAt,BinaryCachePrefixPlan.classificationAt,
        ← BinaryRationalComparisonMeasured.compare_erases,BinaryRationalComparisonMeasured.compare_storage,
        BinaryRationalComparisonMeasured.compare_work,ih]

theorem classification_work {n : ℕ} (input : BinaryTerminalGrouping.Input n) (items : List (Fin n)) (depth : ℕ) :
    (classificationAt input items depth).2 ≤ 4*(classificationAt input items depth).1.2 := by
  induction items generalizing depth with
  | nil => rfl
  | cons j rest ih =>
      have h := ih (depth+1)
      simp only [classificationAt]
      omega

def packAuxAt {α : Type*} (length : α → SignedWord) (budget : SignedWord) :
    List α → SignedWord → List α → ℕ → ((List (List α × SignedWord) × Plan) × ℕ) × ℕ
  | current,total,[],depth =>
      ((([(current.reverse,total)],.block [.frames (depth+(current.length+8)),
        .listAllocation (current.length+3),.arrayAllocation 8]),0),0)
  | current,total,item::rest,depth =>
      let added := BinaryCubicOpcodeMeasured.apply .add total (length item)
      let comparison := BinaryRationalComparisonMeasured.compare added.data budget
      let localPlan := Plan.block [.frames (depth+(current.length+8)),.arrayAllocation 8,
        .listAllocation (current.length+4),.listAllocation added.storage,.listAllocation comparison.storage]
      let localSource := added.source+comparison.work
      let localWork := added.work+comparison.work
      if comparison.data then
        let returned := packAuxAt length budget (item::current) added.data rest (depth+1)
        let later := returned.1
        (((later.1.1,.join localPlan later.1.2),localSource+later.2),localWork+returned.2)
      else
        let returned := packAuxAt length budget [item] (length item) rest (depth+1)
        let later := returned.1
        ((((current.reverse,total)::later.1.1,.join localPlan later.1.2),localSource+later.2),localWork+returned.2)

theorem packAux_compat {α : Type*} (length : α → SignedWord) (budget : SignedWord)
    (current : List α) (total : SignedWord) (items : List α) (depth : ℕ) :
    (packAuxAt length budget current total items depth).1 =
      BinaryCachePrefixPlan.packAuxAt length budget current total items depth := by
  induction items generalizing current total depth with
  | nil => rfl
  | cons item rest ih =>
      simp only [packAuxAt,BinaryCachePrefixPlan.packAuxAt,
        ← BinaryCubicOpcodeMeasured.apply_erases,← BinaryRationalComparisonMeasured.compare_erases,
        BinaryCubicOpcodeMeasured.apply_storage,BinaryCubicOpcodeMeasured.apply_source,
        BinaryRationalComparisonMeasured.compare_storage,BinaryRationalComparisonMeasured.compare_work,ih]
      split <;> rfl

theorem packAux_work {α : Type*} (length : α → SignedWord) (budget : SignedWord)
    (current : List α) (total : SignedWord) (items : List α) (depth : ℕ) :
    (packAuxAt length budget current total items depth).2 ≤
      4*(packAuxAt length budget current total items depth).1.2 := by
  induction items generalizing current total depth with
  | nil => rfl
  | cons item rest ih =>
      have ha := BinaryCubicOpcodeMeasured.apply_work_bound .add total (length item)
      have hYes := ih (item::current) (BinaryCubicOpcodeMeasured.apply .add total (length item)).data (depth+1)
      have hNo := ih [item] (length item) (depth+1)
      simp only [packAuxAt]
      split <;> dsimp only <;> omega

def packingAt {α : Type*} (length : α → SignedWord) (budget : SignedWord) :
    List α → ℕ → ((List (List α × SignedWord) × Plan) × ℕ) × ℕ
  | [],depth => ((([],.block [.frames (depth+1),.arrayAllocation 8]),0),0)
  | item::rest,depth =>
      let returned := packAuxAt length budget [item] (length item) rest (depth+1)
      let later := returned.1
      (((later.1.1,.join (.block [.frames (depth+1),.listAllocation 1,.arrayAllocation 8]) later.1.2),later.2),returned.2)

theorem packing_compat {α : Type*} (length : α → SignedWord) (budget : SignedWord) (items : List α) (depth : ℕ) :
    (packingAt length budget items depth).1 = BinaryCachePrefixPlan.packingAt length budget items depth := by
  cases items <;> simp only [packingAt,BinaryCachePrefixPlan.packingAt,packAux_compat]

theorem packing_work {α : Type*} (length : α → SignedWord) (budget : SignedWord) (items : List α) (depth : ℕ) :
    (packingAt length budget items depth).2 ≤ 4*(packingAt length budget items depth).1.2 := by
  cases items with
  | nil => rfl
  | cons item rest => exact packAux_work length budget [item] (length item) rest (depth+1)

def prefixAt {n : ℕ} (input : BinaryTerminalGrouping.Input n) (depth : ℕ) :
    (((Classification n × List (List (Fin n) × SignedWord)) × Plan) × ℕ) × ℕ :=
  let c := classificationAt input (List.finRange n) (depth+2)
  let classified := c.1
  let p := packingAt input.length.read input.budget classified.1.1.uniforms (depth+2)
  let packed := p.1
  ((((classified.1.1,packed.1.1),.join (.block [.frames (depth+(n+8)),.listAllocation n,.arrayAllocation 8])
    (.join classified.1.2 packed.1.2)),classified.2+packed.2),c.2+p.2)

theorem prefix_compat {n : ℕ} (input : BinaryTerminalGrouping.Input n) (depth : ℕ) :
    (prefixAt input depth).1 = BinaryCachePrefixPlan.prefixAt input depth := by
  simp only [prefixAt,BinaryCachePrefixPlan.prefixAt,classification_compat,packing_compat]

theorem prefix_work {n : ℕ} (input : BinaryTerminalGrouping.Input n) (depth : ℕ) :
    (prefixAt input depth).2 ≤ 4*(prefixAt input depth).1.2 := by
  have hc := classification_work input (List.finRange n) (depth+2)
  have hp := packing_work input.length.read input.budget
    (classificationAt input (List.finRange n) (depth+2)).1.1.1.uniforms (depth+2)
  simp only [prefixAt]
  omega

end Blotto.BinaryCacheArithmeticPrefix
