import Blotto.GeneralPaperEpochFieldInitialPrice

/-! One indexed field-family loop initializes every local epoch state.
Actual cache descriptors derive all eight lengths. The returned native state
retains the exact plans and starts every occurrence/cell level at zero.
-/
namespace Blotto.GeneralPaperEpochInitialFamilyPrice
open GeneralPaperCatalogueEpochCache
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def element {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (cache : Cache m k) (j : Fin m) :
    GeneralPaperEpochFieldState.State k × ℕ :=
  let field := GeneralPaperEpochFieldInitialPrice.run bits index price W (cache.plans.read j)
  (field.1,field.2+32*W)

def run {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (cache : Cache m k) : State cache × ℕ :=
  let filled := PaperIndexedArrayConstruction.run index (if bits then arrayWord W m else W) (element bits index price W cache)
  (⟨filled.1,by
    intro j
    dsimp only [filled]
    rw [PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
    exact GeneralPaperEpochFieldInitialPrice.retained_plan bits index price W (cache.plans.read j)⟩,filled.2+64*W)

def profile (price : ℕ → ℕ) (W m k : ℕ) : ℕ :=
  m*(GeneralPaperEpochFieldInitialPrice.profile price W (GeneralPaperBatchCounterPrice.limit k)+32*W)+
    44*(m+1)*arrayWord W m+64*W

def arithmeticProfile (m k : ℕ) : ℕ :=
  m*(GeneralPaperEpochFieldInitialPrice.arithmeticProfile (GeneralPaperBatchCounterPrice.limit k)+32)+44*(m+1)+64

theorem data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (cache : Cache m k) :
    (run bits index price W cache).1=GeneralPaperCatalogueEpochCache.initial cache := by
  unfold run GeneralPaperCatalogueEpochCache.initial GeneralPaperAdaptiveEpoch.initial
  dsimp only
  congr 1
  rw [PaperIndexedArrayConstruction.run_data]
  congr 1
  funext j
  exact GeneralPaperEpochFieldInitialPrice.data bits index price W (cache.plans.read j)

theorem element_bit_work {m k : ℕ} (price : ℕ → ℕ) (W : ℕ) (cache : Cache m k) (j : Fin m) :
    (element true (fun w => w) price W cache j).2≤
      GeneralPaperEpochFieldInitialPrice.profile price W (GeneralPaperBatchCounterPrice.limit k)+32*W := by
  have hs : (GeneralPaperSourceParameters.prepare k).summarySize≤GeneralPaperBatchCounterPrice.limit k := by
    unfold GeneralPaperBatchCounterPrice.limit; omega
  exact Nat.add_le_add_right (GeneralPaperEpochFieldInitialPrice.bit_work price W _ (cache.plans.read j) hs
    (GeneralPaperActualEpochInstructions.cell_count .p cache j) (GeneralPaperActualEpochInstructions.cell_count .q cache j)
    (GeneralPaperActualEpochInstructions.cell_count .lambda cache j) (GeneralPaperActualEpochInstructions.cell_count .mu cache j)) _

theorem element_arithmetic_work {m k : ℕ} (cache : Cache m k) (j : Fin m) :
    (element false (fun _ => 1) (fun _ => 1) 1 cache j).2≤
      GeneralPaperEpochFieldInitialPrice.arithmeticProfile (GeneralPaperBatchCounterPrice.limit k)+32 := by
  have hs : (GeneralPaperSourceParameters.prepare k).summarySize≤GeneralPaperBatchCounterPrice.limit k := by
    unfold GeneralPaperBatchCounterPrice.limit; omega
  exact Nat.add_le_add_right (GeneralPaperEpochFieldInitialPrice.arithmetic_work _ (cache.plans.read j) hs
    (GeneralPaperActualEpochInstructions.cell_count .p cache j) (GeneralPaperActualEpochInstructions.cell_count .q cache j)
    (GeneralPaperActualEpochInstructions.cell_count .lambda cache j) (GeneralPaperActualEpochInstructions.cell_count .mu cache j)) _

theorem bit_work {m k : ℕ} (price : ℕ → ℕ) (W : ℕ) (cache : Cache m k) :
    (run true (fun w => w) price W cache).2≤profile price W m k := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W m) _ (element true (fun w => w) price W cache)
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (GeneralPaperSummaryArrayControls.array_index W m)
    (element_bit_work price W cache)
  exact Nat.add_le_add_right h _

theorem arithmetic_work {m k : ℕ} (cache : Cache m k) :
    (run false (fun _ => 1) (fun _ => 1) 1 cache).2≤arithmeticProfile m k := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 _ (element false (fun _ => 1) (fun _ => 1) 1 cache)
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _) (element_arithmetic_work cache)
  have h' := Nat.add_le_add_right h 64
  simpa only [run,Bool.false_eq_true,ite_false,Nat.mul_one,arithmeticProfile] using h'

theorem returned_zero {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (cache : Cache m k) (j : Fin m) :
    GeneralPaperEpochFieldState.Bounded ((run bits index price W cache).1.fields.read j) 0 := by
  rw [data]
  change GeneralPaperEpochFieldState.Bounded
    ((FixedArrayTable.ofFn (fun i => GeneralPaperEpochFieldState.initial (cache.plans.read i))).read j) 0
  rw [FixedArrayTable.read_ofFn]
  exact GeneralPaperEpochFieldState.initial_bounded _

theorem same_data {m k : ℕ} (price : ℕ → ℕ) (W : ℕ) (cache : Cache m k) :
    (run true (fun w => w) price W cache).1=(run false (fun _ => 1) (fun _ => 1) 1 cache).1 := by rw [data,data]

theorem prepared_epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let shared := ready.1.2
    let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
    let cache := GeneralPaperCatalogueShared.cache shared a k trees
    (run true (fun w => w) model.rat W cache).2≤profile model.rat W m k ∧
    (run false (fun _ => 1) (fun _ => 1) 1 cache).2≤arithmeticProfile m k :=
  ⟨bit_work model.rat W _,arithmetic_work _⟩

end Blotto.GeneralPaperEpochInitialFamilyPrice
