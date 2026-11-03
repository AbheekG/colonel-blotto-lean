import Blotto.GeneralPaperActualCellCatalogue

/-! One retained zero entry and one padded array fill. The native padding
annotation is formed once from its closed formula, with its arithmetic
charged; no work-sum traversal follows the fill.
-/
namespace Blotto.GeneralPaperCatalogueSlotsExecution
open GeneralPaperCodeAlphabet
open GeneralPaperCodeMinimumScan (Entry)
open GeneralPaperDecodeBucketExecution (primitive)
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def element {n cap : ℕ} (price : ℕ → ℕ) (W : ℕ) (fallback : Entry)
    (raw : FixedArrayTable n (Option Entry)) (i : Fin (cap+1)) : Entry × ℕ :=
  let common := GeneralPaperIntegerWordPrice.compare price i.val 0+64*W
  if i.val=0 then (fallback,common) else
    let j := i.val-1
    let work := common+GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) i.val 1+
      GeneralPaperIntegerWordPrice.compare price j n+128*W
    if h : j<n then ((raw.read ⟨j,h⟩).getD fallback,work) else (fallback,work)

def annotation (price : ℕ → ℕ) (cap : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) cap 1+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 62 (cap+1)+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (62*(cap+1)) 18

def run {n cap : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (raw : FixedArrayTable n (Option Entry)) : (FixedArrayTable (cap+1) Entry × ℕ) × ℕ :=
  let fallback := GeneralPaperCatalogueSlots.zero a
  let filled := PaperIndexedArrayConstruction.run index (if bits then arrayWord W (cap+1) else W)
    (element (primitive bits model) W fallback raw)
  ((filled.1,62*(cap+1)+18),filled.2+annotation (primitive bits model) cap+128*W)

theorem element_data {n cap : ℕ} (price : ℕ → ℕ) (W : ℕ) (a : Alphabet)
    (raw : FixedArrayTable n (Option Entry)) (i : Fin (cap+1)) :
    (element price W (GeneralPaperCatalogueSlots.zero a) raw i).1=GeneralPaperCatalogueSlots.value a raw i := by
  unfold element GeneralPaperCatalogueSlots.value
  split
  · rfl
  · dsimp only
    split <;> rfl

theorem array_data {n cap : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (raw : FixedArrayTable n (Option Entry)) :
    (run (cap:=cap) bits index model W a raw).1.1=(GeneralPaperCatalogueSlots.build (cap:=cap) a raw).1 := by
  unfold run GeneralPaperCatalogueSlots.build
  dsimp only
  rw [PaperIndexedArrayConstruction.run_data,PaperIndexedArrayConstruction.run_data]
  congr 1
  funext i
  exact element_data _ W a raw i

theorem data {n cap : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (raw : FixedArrayTable n (Option Entry)) :
    (run (cap:=cap) bits index model W a raw).1=GeneralPaperCatalogueSlots.build (cap:=cap) a raw := by
  exact Prod.ext (array_data bits index model W a raw) (GeneralPaperCatalogueSlots.build_work a raw).symm

theorem same_data {n cap : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (raw : FixedArrayTable n (Option Entry)) :
    (run (cap:=cap) true (fun w => w) model W a raw).1=(run (cap:=cap) false (fun _ => 1) model 1 a raw).1 := by
  rw [data,data]

theorem every_prefix {n cap : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (raw : FixedArrayTable n (Option Entry)) (count : ℕ) (hCount : count≤cap+1) :
    (PaperIndexedArrayConstruction.fill index (if bits then arrayWord W (cap+1) else W)
      (element (primitive bits model) W (GeneralPaperCatalogueSlots.zero a) raw) count hCount).1.size=count := by
  rw [PaperIndexedArrayConstruction.fill_data,Array.size_ofFn]

end Blotto.GeneralPaperCatalogueSlotsExecution
