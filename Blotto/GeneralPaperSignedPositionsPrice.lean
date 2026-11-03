import Blotto.GeneralPaperCDFPairPrice

/-! Sign projection of every query code into the unsigned interval. One
array fill and one closed native work formula, with no work-sum pass.
-/
namespace Blotto.GeneralPaperSignedPositionsPrice
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperSignedCutOperands (magnitude width)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def element {m : ℕ} (price : ℕ → ℕ) (W U : ℕ) (codes : FixedArrayTable m ℕ) (q : Fin m) : ℕ × ℕ :=
  let result := GeneralPaperCataloguePointExecution.project price W U (codes.read q)
  (result.1,result.2+32*W)

def annotation (price : ℕ → ℕ) (m : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 58 m+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (58*m) 18

def run {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ) (codes : FixedArrayTable m ℕ) :
    (FixedArrayTable m ℕ × ℕ) × ℕ :=
  let filled := PaperIndexedArrayConstruction.run index (if bits then arrayWord W m else W) (element price W U codes)
  ((filled.1,58*m+18),filled.2+annotation price m+64*W)

theorem data {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ) (codes : FixedArrayTable m ℕ) :
    (run bits index price W U codes).1=GeneralPaperSignedUpdatePlan.projected U codes := by
  apply Prod.ext
  · unfold run GeneralPaperSignedUpdatePlan.projected
    dsimp only
    rw [PaperIndexedArrayConstruction.run_data,PaperIndexedArrayConstruction.run_data]
    congr 1
    funext q
    exact GeneralPaperCataloguePointExecution.project_data price W U (codes.read q)
  · exact (GeneralPaperSignedUpdatePlan.projected_work U codes).symm

theorem positions {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ) (codes : FixedArrayTable m ℕ)
    (hCodes : ∀ q,codes.read q<2*U) (q : Fin m) : (run bits index price W U codes).1.1.read q<U := by
  rw [data,GeneralPaperSignedUpdatePlan.projected_read]
  exact GeneralPaperUnsignedPartition.project_bound U (codes.read q) (hCodes q)

theorem annotation_work (price : ℕ → ℕ) (hMono : Monotone price) (m U : ℕ) : annotation price m≤4*price (width m U) := by
  have hW := GeneralPaperSignedCutOperands.word_bound m U
  have p (op : ℕ → ℕ → ℕ) (a b : ℕ) (ha : a≤magnitude m U) (hb : b≤magnitude m U) (hc : op a b≤magnitude m U) :
      GeneralPaperNaturalPrimitivePrice.binary price op a b≤2*price (width m U) :=
    (GeneralPaperNaturalPrimitivePrice.binary_le price hMono op a b (magnitude m U) ha hb hc).trans
      (Nat.mul_le_mul_left 2 (hMono hW))
  have ha := p (fun a b => a*b) 58 m (by unfold magnitude; omega) (by unfold magnitude; omega) (by unfold magnitude; omega)
  have hb := p (fun a b => a+b) (58*m) 18 (by unfold magnitude; omega) (by unfold magnitude; omega) (by unfold magnitude; omega)
  unfold annotation
  omega

def profile (price : ℕ → ℕ) (W m U : ℕ) : ℕ :=
  m*(3*price (GeneralPaperCataloguePointOperands.width U)+64*W)+44*(m+1)*arrayWord W m+4*price (width m U)+64*W

def arithmeticProfile (m : ℕ) : ℕ := m*67+44*(m+1)+68

theorem bit_work {m : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W U : ℕ) (codes : FixedArrayTable m ℕ)
    (hCodes : ∀ q,codes.read q<2*U) : (run true (fun w => w) price W U codes).2≤profile price W m U := by
  have hEntry (q : Fin m) : (element price W U codes q).2≤3*price (GeneralPaperCataloguePointOperands.width U)+64*W := by
    have h := GeneralPaperCataloguePointOperands.project_work price hMono W U (codes.read q) (hCodes q)
    exact (Nat.add_le_add_right h (32*W)).trans_eq (by omega)
  have hA := GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W m)
    (3*price (GeneralPaperCataloguePointOperands.width U)+64*W) (element price W U codes)
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (GeneralPaperSummaryArrayControls.array_index W m) hEntry
  exact Nat.add_le_add_right (Nat.add_le_add hA (annotation_work price hMono m U)) _

theorem arithmetic_work {m : ℕ} (U : ℕ) (codes : FixedArrayTable m ℕ) :
    (run false (fun _ => 1) (fun _ => 1) 1 U codes).2≤arithmeticProfile m := by
  have hEntry (q : Fin m) : (element (fun _ => 1) 1 U codes q).2≤67 := by
    unfold element GeneralPaperCataloguePointExecution.project
    dsimp only
    split <;> simp only [GeneralPaperIntegerWordPrice.compare,GeneralPaperNaturalPrimitivePrice.binary] <;> omega
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 67 (element (fun _ => 1) 1 U codes)
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _) hEntry
  change (PaperIndexedArrayConstruction.run (fun _ => 1) 1 (element (fun _ => 1) 1 U codes)).2+4+64≤_
  unfold arithmeticProfile
  omega

theorem every_prefix {m : ℕ} (index price : ℕ → ℕ) (W A U : ℕ) (codes : FixedArrayTable m ℕ)
    (count : ℕ) (hCount : count≤m) :
    (PaperIndexedArrayConstruction.fill index A (element price W U codes) count hCount).1.size=count := by
  rw [PaperIndexedArrayConstruction.fill_data,Array.size_ofFn]

end Blotto.GeneralPaperSignedPositionsPrice
