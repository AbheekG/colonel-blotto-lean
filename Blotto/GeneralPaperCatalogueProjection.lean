import Blotto.GeneralPaperCachedCatalogueFamily

/-! Three reference projections of retained catalogue entries. Each
projection has one row loop and one field loop, with all reference reads,
writes and local index controls charged. No numerical value is recomputed.
-/
namespace Blotto.GeneralPaperCatalogueProjection
open GeneralPaperCodeMinimumScan (Entry)
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

inductive Field where
  | code | threshold | opened

def FieldType : Field → Type
  | .code => ℕ
  | .threshold => Farey.Fraction
  | .opened => Bool

def select : (field : Field) → Entry → FieldType field
  | .code,e => e.cost
  | .threshold,e => e.predecessor.threshold
  | .opened,e => e.predecessor.opened

def row {K : ℕ} (bits : Bool) (index : ℕ → ℕ) (W : ℕ) (field : Field) (values : FixedArrayTable K Entry) :
    FixedArrayTable K (FieldType field) × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W K else W)
    (fun i => (select field (values.read i),32*W))

def element {m K : ℕ} (bits : Bool) (index : ℕ → ℕ) (W : ℕ) (field : Field)
    (values : FixedArrayTable m (FixedArrayTable K Entry)) (j : Fin m) : FixedArrayTable K (FieldType field) × ℕ :=
  let found := row bits index W field (values.read j)
  (found.1,found.2+16*W)

def family {m K : ℕ} (bits : Bool) (index : ℕ → ℕ) (W : ℕ) (field : Field)
    (values : FixedArrayTable m (FixedArrayTable K Entry)) : FixedArrayTable m (FixedArrayTable K (FieldType field)) × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W m else W) (element bits index W field values)

theorem row_data {K : ℕ} (bits : Bool) (index : ℕ → ℕ) (W : ℕ) (field : Field) (values : FixedArrayTable K Entry) :
    (row bits index W field values).1=FixedArrayTable.ofFn (fun i => select field (values.read i)) :=
  PaperIndexedArrayConstruction.run_data _ _ _

theorem family_data {m K : ℕ} (bits : Bool) (index : ℕ → ℕ) (W : ℕ) (field : Field)
    (values : FixedArrayTable m (FixedArrayTable K Entry)) :
    (family bits index W field values).1=FixedArrayTable.ofFn (fun j => FixedArrayTable.ofFn (fun i => select field ((values.read j).read i))) := by
  rw [family,PaperIndexedArrayConstruction.run_data]
  congr 1
  funext j
  exact row_data bits index W field (values.read j)

def run {m K : ℕ} (bits : Bool) (index : ℕ → ℕ) (W : ℕ) (values : FixedArrayTable m (FixedArrayTable K Entry)) :
    GeneralPaperCatalogueArrays.Arrays m K × ℕ :=
  let codes := family bits index W .code values
  let thresholds := family bits index W .threshold values
  let opened := family bits index W .opened values
  (⟨values,codes.1,thresholds.1,opened.1,family_data bits index W .code values,
    family_data bits index W .threshold values,family_data bits index W .opened values⟩,
    codes.2+thresholds.2+opened.2+128*W)

def rowProfile (W K : ℕ) : ℕ := K*(32*W)+44*(K+1)*arrayWord W K

def familyProfile (W m K : ℕ) : ℕ := m*(rowProfile W K+16*W)+44*(m+1)*arrayWord W m

def profile (W m K : ℕ) : ℕ := 3*familyProfile W m K+128*W

def rowArithmeticProfile (K : ℕ) : ℕ := K*32+44*(K+1)

def familyArithmeticProfile (m K : ℕ) : ℕ := m*(rowArithmeticProfile K+16)+44*(m+1)

def arithmeticProfile (m K : ℕ) : ℕ := 3*familyArithmeticProfile m K+128

theorem data {m K : ℕ} (bits : Bool) (index : ℕ → ℕ) (W : ℕ) (values : FixedArrayTable m (FixedArrayTable K Entry)) :
    (run bits index W values).1=GeneralPaperCatalogueArrays.project values := by
  unfold run GeneralPaperCatalogueArrays.project
  dsimp only
  simp only [family_data,select]
  rfl

theorem row_bit_work {K : ℕ} (W : ℕ) (field : Field) (values : FixedArrayTable K Entry) :
    (row true (fun w => w) W field values).2≤rowProfile W K :=
  GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W K) (32*W) _
    (GeneralPaperSummaryArrayControls.array_word_positive W K) (GeneralPaperSummaryArrayControls.array_index W K) (fun _ => Nat.le_refl _)

theorem family_bit_work {m K : ℕ} (W : ℕ) (field : Field) (values : FixedArrayTable m (FixedArrayTable K Entry)) :
    (family true (fun w => w) W field values).2≤familyProfile W m K := by
  apply GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W m) (rowProfile W K+16*W) _
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (GeneralPaperSummaryArrayControls.array_index W m)
  intro j
  exact Nat.add_le_add_right (row_bit_work W field (values.read j)) _

theorem bit_work {m K : ℕ} (W : ℕ) (values : FixedArrayTable m (FixedArrayTable K Entry)) :
    (run true (fun w => w) W values).2≤profile W m K := by
  have hc := family_bit_work W .code values
  have ht := family_bit_work W .threshold values
  have ho := family_bit_work W .opened values
  have h := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hc ht) ho) (128*W)
  exact h.trans_eq (by unfold profile; omega)

theorem row_arithmetic_work {K : ℕ} (field : Field) (values : FixedArrayTable K Entry) :
    (row false (fun _ => 1) 1 field values).2≤rowArithmeticProfile K := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 32
    (fun i : Fin K => (select field (values.read i),32)) (Nat.le_refl _) (fun _ _ => Nat.le_refl _) (fun _ => Nat.le_refl _)
  simpa only [row,Bool.false_eq_true,ite_false,rowArithmeticProfile,Nat.mul_one] using h

theorem family_arithmetic_work {m K : ℕ} (field : Field) (values : FixedArrayTable m (FixedArrayTable K Entry)) :
    (family false (fun _ => 1) 1 field values).2≤familyArithmeticProfile m K := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 (rowArithmeticProfile K+16)
    (element false (fun _ => 1) 1 field values) (Nat.le_refl _) (fun _ _ => Nat.le_refl _)
    (fun j => Nat.add_le_add_right (row_arithmetic_work field (values.read j)) 16)
  simpa only [family,Bool.false_eq_true,ite_false,familyArithmeticProfile,Nat.mul_one] using h

theorem arithmetic_work {m K : ℕ} (values : FixedArrayTable m (FixedArrayTable K Entry)) :
    (run false (fun _ => 1) 1 values).2≤arithmeticProfile m K := by
  have hc := family_arithmetic_work .code values
  have ht := family_arithmetic_work .threshold values
  have ho := family_arithmetic_work .opened values
  have h := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hc ht) ho) 128
  exact h.trans_eq (by unfold arithmeticProfile; omega)

theorem every_row_prefix {K : ℕ} (index : ℕ → ℕ) (W : ℕ) (field : Field) (values : FixedArrayTable K Entry)
    (count : ℕ) (hCount : count≤K) :
    (PaperIndexedArrayConstruction.fill index W (fun i => (select field (values.read i),32*W)) count hCount).1.size=count := by
  rw [PaperIndexedArrayConstruction.fill_data,Array.size_ofFn]

end Blotto.GeneralPaperCatalogueProjection
