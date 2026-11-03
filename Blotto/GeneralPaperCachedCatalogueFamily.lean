import Blotto.GeneralPaperActualCachedCatalogue

/-! One complete cached catalogue per field, followed by one reference
projection of its retained entries. The native work fields are preserved;
no catalogue or summary is replayed by the projection.
-/
namespace Blotto.GeneralPaperCachedCatalogueFamily
open GeneralPaperCodeAlphabet
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def element {m n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) (j : Fin m) :
    GeneralPaperCachedCatalogue.Prepared (n+1) × ℕ :=
  let found := GeneralPaperCachedCatalogueExecution.run bits index model W a response (summaries.read j)
  (found.1,found.2+32*W)

def run {m n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) :
    FixedArrayTable m (GeneralPaperCachedCatalogue.Prepared (n+1)) × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W m else W)
    (element bits index model W a response summaries)

def entries {m cap : ℕ} (bits : Bool) (index : ℕ → ℕ) (W : ℕ)
    (catalogues : FixedArrayTable m (GeneralPaperCachedCatalogue.Prepared cap)) :
    FixedArrayTable m (FixedArrayTable (cap+1) GeneralPaperCodeMinimumScan.Entry) × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W m else W)
    (fun j => ((catalogues.read j).entries,32*W))

def profile (model : RationalCostModel) (W m n : ℕ) (a : Alphabet) : ℕ :=
  m*(GeneralPaperCachedCataloguePrice.profile model W n a+32*W)+44*(m+1)*arrayWord W m

def arithmeticProfile (m n : ℕ) (a : Alphabet) : ℕ :=
  m*(GeneralPaperCachedCataloguePrice.arithmeticProfile n a+32)+44*(m+1)

def entriesProfile (W m : ℕ) : ℕ := m*(32*W)+44*(m+1)*arrayWord W m

def entriesArithmeticProfile (m : ℕ) : ℕ := m*32+44*(m+1)

theorem data {m n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) :
    (run bits index model W a response summaries).1=
      FixedArrayTable.ofFn (fun j => GeneralPaperCachedCatalogue.prepare a response (summaries.read j)) := by
  rw [run,PaperIndexedArrayConstruction.run_data]
  congr 1
  funext j
  exact GeneralPaperCachedCatalogueExecution.data bits index model W a response (summaries.read j)

theorem entries_data {m cap : ℕ} (bits : Bool) (index : ℕ → ℕ) (W : ℕ)
    (catalogues : FixedArrayTable m (GeneralPaperCachedCatalogue.Prepared cap)) :
    (entries bits index W catalogues).1=FixedArrayTable.ofFn (fun j => (catalogues.read j).entries) :=
  PaperIndexedArrayConstruction.run_data _ _ _

theorem bit_work {m n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) (hCodes : ∀ j r,(summaries.read j).read r<2*(8*a.C)) :
    (run true (fun w => w) model W a response summaries).2≤profile model W m n a := by
  apply GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W m)
    (GeneralPaperCachedCataloguePrice.profile model W n a+32*W) _
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (GeneralPaperSummaryArrayControls.array_index W m)
  intro j
  exact Nat.add_le_add_right (GeneralPaperCachedCataloguePrice.bit_work model W a response (summaries.read j) (hCodes j)) _

theorem arithmetic_work {m n : ℕ} (model : RationalCostModel) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) (hCodes : ∀ j r,(summaries.read j).read r<2*(8*a.C)) :
    (run false (fun _ => 1) model 1 a response summaries).2≤arithmeticProfile m n a := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1
    (GeneralPaperCachedCataloguePrice.arithmeticProfile n a+32)
    (element false (fun _ => 1) model 1 a response summaries) (Nat.le_refl _) (fun _ _ => Nat.le_refl _)
    (fun j => Nat.add_le_add_right (GeneralPaperCachedCataloguePrice.arithmetic_work model a response (summaries.read j) (hCodes j)) 32)
  simpa only [run,Bool.false_eq_true,ite_false,arithmeticProfile,Nat.mul_one] using h

theorem entries_bit_work {m cap : ℕ} (W : ℕ) (catalogues : FixedArrayTable m (GeneralPaperCachedCatalogue.Prepared cap)) :
    (entries true (fun w => w) W catalogues).2≤entriesProfile W m :=
  GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W m) (32*W) _
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (GeneralPaperSummaryArrayControls.array_index W m) (fun _ => Nat.le_refl _)

theorem entries_arithmetic_work {m cap : ℕ} (catalogues : FixedArrayTable m (GeneralPaperCachedCatalogue.Prepared cap)) :
    (entries false (fun _ => 1) 1 catalogues).2≤entriesArithmeticProfile m := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 32
    (fun j : Fin m => ((catalogues.read j).entries,32)) (Nat.le_refl _) (fun _ _ => Nat.le_refl _) (fun _ => Nat.le_refl _)
  simpa only [entries,Bool.false_eq_true,ite_false,entriesArithmeticProfile,Nat.mul_one] using h

theorem every_prefix {m n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W A : ℕ)
    (a : Alphabet) (response : Bool) (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) (count : ℕ) (hCount : count≤m) :
    (PaperIndexedArrayConstruction.fill index A (element bits index model W a response summaries) count hCount).1.size=count := by
  rw [PaperIndexedArrayConstruction.fill_data,Array.size_ofFn]

end Blotto.GeneralPaperCachedCatalogueFamily
