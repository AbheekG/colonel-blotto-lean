import Blotto.GeneralPaperNativeSummaryArray

/-! Construct a field family of summaries in the indexed reference-array
model. A callback reads one retained node and returns one summary reference.
Both inner occurrence and outer field traversals have derived index words.
-/
namespace Blotto.GeneralPaperSummaryFamilyPrice
open GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def run (bits : Bool) (index primitive : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (digits height : ℕ) (nodes : FixedArrayTable m (Node height)) : FixedArrayTable m (Summary k) × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W m else W) (fun field =>
    let summary := GeneralPaperNativeSummaryArray.run bits index primitive W m lambda k Qv c hc digits height (nodes.read field)
    (summary.1,summary.2+16*W))

def profile (primitive : ℕ → ℕ) (W m lambda k Qv height : ℕ) : ℕ :=
  m*(GeneralPaperSummaryArrayPrice.profile primitive W m lambda k Qv height+16*W)+44*(m+1)*arrayWord W m

def arithmeticProfile (m lambda k Qv height : ℕ) : ℕ :=
  m*(GeneralPaperSummaryArrayPrice.arithmeticProfile m lambda k Qv height+16)+44*(m+1)

theorem data (bits : Bool) (index primitive : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (digits height : ℕ) (nodes : FixedArrayTable m (Node height)) (hHeight : height≤lambda+1)
    (hValid : ∀ field,Valid lambda k (nodes.read field))
    (hPath : ∀ field,PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 (nodes.read field)) :
    (run bits index primitive W m lambda k Qv c hc digits height nodes).1=
      GeneralPaperCatalogueTreeCache.summaries c.powers digits k nodes := by
  unfold run GeneralPaperCatalogueTreeCache.summaries
  rw [PaperIndexedArrayConstruction.run_data]
  congr 1
  funext field
  dsimp only
  exact GeneralPaperNativeSummaryArray.data bits index primitive W m lambda k Qv c hc digits height (nodes.read field)
    hHeight (hValid field) (hPath field)

theorem bit_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (digits height : ℕ) (hDigits : digits=GeneralPaperQuantileComparison.width lambda k)
    (nodes : FixedArrayTable m (Node height)) (hHeight : height≤lambda+1)
    (hValid : ∀ field,Valid lambda k (nodes.read field))
    (hPath : ∀ field,PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 (nodes.read field)) :
    (run true (fun w => w) primitive W m lambda k Qv c hc digits height nodes).2≤profile primitive W m lambda k Qv height := by
  apply GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W m)
    (GeneralPaperSummaryArrayPrice.profile primitive W m lambda k Qv height+16*W) _
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (GeneralPaperSummaryArrayControls.array_index W m)
  intro field
  exact Nat.add_le_add_right (GeneralPaperNativeSummaryArray.bit_work primitive hMono W m lambda k Qv c hc digits height hDigits
    (nodes.read field) hHeight (hValid field) (hPath field)) _

theorem arithmetic_work (m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (digits height : ℕ)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (nodes : FixedArrayTable m (Node height)) :
    (run false (fun _ => 1) (fun _ => 1) 1 m lambda k Qv c hc digits height nodes).2≤arithmeticProfile m lambda k Qv height := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1
    (GeneralPaperSummaryArrayPrice.arithmeticProfile m lambda k Qv height+16) (fun field : Fin m =>
      let summary := GeneralPaperNativeSummaryArray.run false (fun _ => 1) (fun _ => 1) 1 m lambda k Qv c hc digits height (nodes.read field)
      (summary.1,summary.2+16)) (Nat.le_refl 1) (fun _ _ => Nat.le_refl 1)
    (fun field => Nat.add_le_add_right
      (GeneralPaperNativeSummaryArray.arithmetic_work m lambda k Qv c hc digits height hDigits (nodes.read field)) 16)
  simpa only [run,arithmeticProfile,Bool.false_eq_true,ite_false,Nat.mul_one] using h

theorem every_prefix (bits : Bool) (index primitive : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (digits height : ℕ) (nodes : FixedArrayTable m (Node height)) (count : ℕ) (hCount : count≤m) :
    (PaperIndexedArrayConstruction.fill index (if bits then arrayWord W m else W) (fun field : Fin m =>
      let summary := GeneralPaperNativeSummaryArray.run bits index primitive W m lambda k Qv c hc digits height (nodes.read field)
      (summary.1,summary.2+16*W)) count hCount).1.size=count := by
  rw [PaperIndexedArrayConstruction.fill_data,Array.size_ofFn]

end Blotto.GeneralPaperSummaryFamilyPrice
