import Blotto.GeneralPaperCatalogueProjection

/-! Retain the full per-field catalogues, project their entry-array
references once and construct the three native numerical reference arrays.
-/
namespace Blotto.GeneralPaperCatalogueArraysExecution
open GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def reference {m n : ℕ} (a : Alphabet) (response : Bool) (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) :
    GeneralPaperCatalogueArrays.Arrays m (n+2) :=
  GeneralPaperCatalogueArrays.project (FixedArrayTable.ofFn (fun j => (GeneralPaperCachedCatalogue.prepare a response (summaries.read j)).entries))

def run {m n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) :
    GeneralPaperCatalogueArrays.Arrays m (n+2) × ℕ :=
  let catalogues := GeneralPaperCachedCatalogueFamily.run bits index model W a response summaries
  let entries := GeneralPaperCachedCatalogueFamily.entries bits index W catalogues.1
  let arrays := GeneralPaperCatalogueProjection.run bits index W entries.1
  (arrays.1,catalogues.2+entries.2+arrays.2+128*W)

def profile (model : RationalCostModel) (W m n : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperCachedCatalogueFamily.profile model W m n a+GeneralPaperCachedCatalogueFamily.entriesProfile W m+
    GeneralPaperCatalogueProjection.profile W m (n+2)+128*W

def arithmeticProfile (m n : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperCachedCatalogueFamily.arithmeticProfile m n a+GeneralPaperCachedCatalogueFamily.entriesArithmeticProfile m+
    GeneralPaperCatalogueProjection.arithmeticProfile m (n+2)+128

theorem data {m n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) :
    (run bits index model W a response summaries).1=reference a response summaries := by
  unfold run
  dsimp only
  rw [GeneralPaperCatalogueProjection.data,GeneralPaperCachedCatalogueFamily.entries_data,GeneralPaperCachedCatalogueFamily.data]
  simp only [reference,FixedArrayTable.read_ofFn]

theorem native_data {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k : ℕ)
    (a : Alphabet) (response : Bool) (summaries : FixedArrayTable m (GeneralPaperUnsignedCellConstancy.Summary k)) :
    (run bits index model W a response summaries).1=GeneralPaperCatalogueArrays.prepare a response k summaries := by
  simpa only [reference,GeneralPaperCatalogueArrays.prepare,FixedArrayTable.read_ofFn] using data bits index model W a response summaries

theorem same_data {m n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) :
    (run true (fun w => w) model W a response summaries).1=(run false (fun _ => 1) model 1 a response summaries).1 := by
  rw [data,data]

theorem bit_work {m n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) (hCodes : ∀ j r,(summaries.read j).read r<2*(8*a.C)) :
    (run true (fun w => w) model W a response summaries).2≤profile model W m n a := by
  have hC := GeneralPaperCachedCatalogueFamily.bit_work model W a response summaries hCodes
  have hE := GeneralPaperCachedCatalogueFamily.entries_bit_work W
    (GeneralPaperCachedCatalogueFamily.run true (fun w => w) model W a response summaries).1
  have hP := GeneralPaperCatalogueProjection.bit_work W
    (GeneralPaperCachedCatalogueFamily.entries true (fun w => w) W
      (GeneralPaperCachedCatalogueFamily.run true (fun w => w) model W a response summaries).1).1
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hC hE) hP) _

theorem arithmetic_work {m n : ℕ} (model : RationalCostModel) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) (hCodes : ∀ j r,(summaries.read j).read r<2*(8*a.C)) :
    (run false (fun _ => 1) model 1 a response summaries).2≤arithmeticProfile m n a := by
  have hC := GeneralPaperCachedCatalogueFamily.arithmetic_work model a response summaries hCodes
  have hE := GeneralPaperCachedCatalogueFamily.entries_arithmetic_work
    (GeneralPaperCachedCatalogueFamily.run false (fun _ => 1) model 1 a response summaries).1
  have hP := GeneralPaperCatalogueProjection.arithmetic_work
    (GeneralPaperCachedCatalogueFamily.entries false (fun _ => 1) 1
      (GeneralPaperCachedCatalogueFamily.run false (fun _ => 1) model 1 a response summaries).1).1
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hC hE) hP) _

end Blotto.GeneralPaperCatalogueArraysExecution
