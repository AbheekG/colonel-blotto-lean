import Blotto.BinaryArithmeticEntryWork
import Blotto.BinaryCacheFinishPlan

/-! Proof-only raw arithmetic entry charges follow actual cache decisions,
returned classification, packed totals and fetched words. Existing retained
cells pay the charge at every composite boundary; no runtime field changes. -/
namespace Blotto.BinaryCacheArithmeticEntryWork
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryTracePlanMeasured
set_option autoImplicit false
set_option maxHeartbeats 5000000

def classification {n : ℕ} (input : BinaryTerminalGrouping.Input n) : List (Fin n) → ℕ → ℕ
  | [],_depth => 0
  | j::rest,depth =>
      BinaryArithmeticEntryWork.comparison (input.resource.read j) (input.length.read j)+
      BinaryArithmeticEntryWork.comparison (input.length.read j) (input.resource.read j)+
      BinaryArithmeticEntryWork.comparison (input.resource.read j) BinaryRationalOpcode.zero+
      classification input rest (depth+1)

theorem classification_bound {n : ℕ} (input : BinaryTerminalGrouping.Input n) (items : List (Fin n)) (depth : ℕ) :
    classification input items depth ≤
      2*listCells (denote (BinaryCacheArithmeticPrefix.classificationAt input items depth).1.1.2) := by
  induction items generalizing depth with
  | nil => simp [classification,BinaryCacheArithmeticPrefix.classificationAt,denote,listCells]
  | cons j rest ih =>
      have hu := BinaryArithmeticEntryWork.comparison_bound (input.resource.read j) (input.length.read j)
      have hd := BinaryArithmeticEntryWork.comparison_bound (input.length.read j) (input.resource.read j)
      have hz := BinaryArithmeticEntryWork.comparison_bound (input.resource.read j) BinaryRationalOpcode.zero
      have ht := ih (depth+1)
      simp only [classification,BinaryCacheArithmeticPrefix.classificationAt,denote,listCells_append,listCells]
      omega

def packAux {α : Type*} (length : α → SignedWord) (budget : SignedWord) :
    List α → SignedWord → List α → ℕ → ℕ
  | _current,_total,[],_depth => 0
  | current,total,item::rest,depth =>
      let added := BinaryCubicOpcodeMeasured.apply .add total (length item)
      let compared := BinaryRationalComparisonMeasured.compare added.data budget
      BinaryArithmeticEntryWork.raw .add total (length item)+
        BinaryArithmeticEntryWork.comparison added.data budget+
        if compared.data then packAux length budget (item::current) added.data rest (depth+1)
        else packAux length budget [item] (length item) rest (depth+1)

theorem packAux_bound {α : Type*} (length : α → SignedWord) (budget : SignedWord)
    (current : List α) (total : SignedWord) (items : List α) (depth : ℕ) :
    packAux length budget current total items depth ≤
      2*listCells (denote (BinaryCacheArithmeticPrefix.packAuxAt length budget current total items depth).1.1.2) := by
  induction items generalizing current total depth with
  | nil => simp [packAux,BinaryCacheArithmeticPrefix.packAuxAt,denote,listCells]
  | cons item rest ih =>
      have ha := BinaryArithmeticEntryWork.cubic_bound .add total (length item)
      have hc := BinaryArithmeticEntryWork.comparison_bound (BinaryCubicOpcodeMeasured.apply .add total (length item)).data budget
      have hy := ih (item::current) (BinaryCubicOpcodeMeasured.apply .add total (length item)).data (depth+1)
      have hn := ih [item] (length item) (depth+1)
      simp only [packAux,BinaryCacheArithmeticPrefix.packAuxAt]
      split <;> simp only [denote,listCells_append,listCells] <;> omega

def packing {α : Type*} (length : α → SignedWord) (budget : SignedWord) : List α → ℕ → ℕ
  | [],_depth => 0
  | item::rest,depth => packAux length budget [item] (length item) rest (depth+1)

theorem packing_bound {α : Type*} (length : α → SignedWord) (budget : SignedWord) (items : List α) (depth : ℕ) :
    packing length budget items depth ≤
      2*listCells (denote (BinaryCacheArithmeticPrefix.packingAt length budget items depth).1.1.2) := by
  cases items with
  | nil => simp [packing,BinaryCacheArithmeticPrefix.packingAt,denote,listCells]
  | cons item rest =>
      have h := packAux_bound length budget [item] (length item) rest (depth+1)
      simp only [packing,BinaryCacheArithmeticPrefix.packingAt,denote,listCells_append,listCells]
      omega

def prefixEntries {n : ℕ} (input : BinaryTerminalGrouping.Input n) (depth : ℕ) : ℕ :=
  let indices := BinaryCacheTableMeasured.indices n
  let c := BinaryCacheArithmeticPrefix.classificationAt input indices.1 (depth+2)
  classification input indices.1 (depth+2)+packing input.length.read input.budget c.1.1.1.uniforms (depth+2)

theorem prefix_bound {n : ℕ} (input : BinaryTerminalGrouping.Input n) (depth : ℕ) :
    prefixEntries input depth ≤ 2*listCells (denote (BinaryCacheFinishPlan.prefixAt input depth).1.1.1.2) := by
  have hc := classification_bound input (BinaryCacheTableMeasured.indices n).1 (depth+2)
  have hp := packing_bound input.length.read input.budget
    (BinaryCacheArithmeticPrefix.classificationAt input (BinaryCacheTableMeasured.indices n).1 (depth+2)).1.1.1.uniforms (depth+2)
  simp only [prefixEntries,BinaryCacheFinishPlan.prefixAt,denote,listCells_append,listCells]
  omega

def members {n m : ℕ} (store : BinaryWordObjectArray.Store n) (total : SignedWord) (g : Fin m) :
    List (Fin n) → ℕ → ℕ
  | [],_depth => 0
  | j::rest,depth =>
      let fetched := (BinaryObjectCachePlan.readLengthAt store j (depth+1)).1
      BinaryArithmeticEntryWork.raw .div (fetched.1.1.getD BinaryRationalOpcode.zero) total+
        members store total g rest (depth+1)

theorem members_bound {n m : ℕ} (store : BinaryWordObjectArray.Store n) (total : SignedWord)
    (g : Fin m) (items : List (Fin n)) (depth : ℕ) :
    members store total g items depth ≤
      2*listCells (denote (BinaryCacheArithmeticPlan.membersAt store total g items depth).1.1.2) := by
  induction items generalizing depth with
  | nil => simp [members,BinaryCacheArithmeticPlan.membersAt,denote,listCells]
  | cons j rest ih =>
      have h := BinaryArithmeticEntryWork.cubic_bound .div
        ((BinaryObjectCachePlan.readLengthAt store j (depth+1)).1.1.1.getD BinaryRationalOpcode.zero) total
      have ht := ih (depth+1)
      simp only [members,BinaryCacheArithmeticPlan.membersAt,denote,listCells_append,listCells]
      omega

def groups {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (table : FixedArrayTable m (List (Fin n) × SignedWord)) : List (Fin m) → ℕ → ℕ
  | [],_depth => 0
  | g::rest,depth => members store (table.read g).2 g (table.read g).1 (depth+2)+groups store table rest (depth+2)

theorem groups_bound {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (table : FixedArrayTable m (List (Fin n) × SignedWord)) (items : List (Fin m)) (depth : ℕ) :
    groups store table items depth ≤
      2*listCells (denote (BinaryCacheArithmeticPlan.groupsAt store table items depth).1.1.2) := by
  induction items generalizing depth with
  | nil => simp [groups,BinaryCacheArithmeticPlan.groupsAt,denote,listCells]
  | cons g rest ih =>
      have hm := members_bound store (table.read g).2 g (table.read g).1 (depth+2)
      have ht := ih (depth+2)
      simp only [groups,BinaryCacheArithmeticPlan.groupsAt,denote,listCells_append,listCells]
      omega

def routes {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (table : FixedArrayTable m (List (Fin n) × SignedWord)) (depth : ℕ) : ℕ :=
  groups store table (BinaryCacheTableMeasured.indices m).1 (depth+2)

theorem routes_bound {n m : ℕ} (store : BinaryWordObjectArray.Store n)
    (table : FixedArrayTable m (List (Fin n) × SignedWord)) (depth : ℕ) :
    routes store table depth ≤ 2*listCells (denote (BinaryCacheFinishPlan.routesAt store table depth).1.1.1.2) := by
  have h := groups_bound store table (BinaryCacheTableMeasured.indices m).1 (depth+2)
  simp only [routes,BinaryCacheFinishPlan.routesAt,denote,listCells_append,listCells]
  omega

def pivot {n : ℕ} (input : BinaryTerminalGrouping.Input n) : Option (Fin n) → ℕ
  | none => 0
  | some j => BinaryArithmeticEntryWork.raw .div (input.resource.read j) (input.length.read j)

theorem pivot_bound {n : ℕ} (input : BinaryTerminalGrouping.Input n) (selected : Option (Fin n)) :
    pivot input selected ≤ 2*listCells (BinaryCacheFinishPlan.pivot input selected).1.1.2 := by
  cases selected with
  | none => simp [pivot,BinaryCacheFinishPlan.pivot,listCells]
  | some j =>
      have h := BinaryArithmeticEntryWork.cubic_bound .div (input.resource.read j) (input.length.read j)
      simpa only [pivot,BinaryCacheFinishPlan.pivot,listCells,Nat.add_zero] using h

def cache {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) (depth : ℕ) : ℕ :=
  let front := (BinaryCacheFinishPlan.prefixAt input depth).1.1
  let packed := (BinaryCacheTableMeasured.packTable front.1.1.2).1
  prefixEntries input depth+routes store packed (depth+2)+pivot input front.1.1.1.pivot

theorem cache_bound {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) (depth : ℕ) :
    cache input store depth ≤ 2*listCells (denote (BinaryCacheFinishPlan.cacheAt input store depth).1.1.1.2) := by
  have hp := prefix_bound input depth
  have hr := routes_bound store (BinaryCacheTableMeasured.packTable (BinaryCacheFinishPlan.prefixAt input depth).1.1.1.1.2).1 (depth+2)
  have he := pivot_bound input (BinaryCacheFinishPlan.prefixAt input depth).1.1.1.1.1.pivot
  simp only [cache,BinaryCacheFinishPlan.cacheAt,denote,listCells_append,listCells_under,listCells]
  omega

theorem emitted_bound {n : ℕ} (input : BinaryTerminalGrouping.Input n) (store : BinaryWordObjectArray.Store n) :
    cache input store 0 ≤ 2*listCells (BinaryCacheFinishPlan.cacheWithEmission input store).1.1.1.1.2 := by
  have h := cache_bound input store 0
  simpa only [BinaryCacheFinishPlan.cacheWithEmission,emitFull_erases,emit_data,List.append_nil] using h

end Blotto.BinaryCacheArithmeticEntryWork
