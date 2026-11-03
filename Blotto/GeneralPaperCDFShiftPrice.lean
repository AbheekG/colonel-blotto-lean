import Blotto.GeneralPaperActualCataloguePreparation

/-! Exact native CDF shifted cuts, including the zero shift. One array fill
and one closed native annotation construction; no work-sum traversal.
-/
namespace Blotto.GeneralPaperCDFShiftPrice
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperSignedCutOperands (magnitude width)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def element {m : ℕ} (price : ℕ → ℕ) (W shift : ℕ) (queries : FixedArrayTable m ℕ) (q : Fin m) : ℕ × ℕ :=
  (queries.read q+shift,GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (queries.read q) shift+32*W)

def annotation (price : ℕ → ℕ) (m : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 54 m+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (54*m) 18

def run {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W shift : ℕ) (queries : FixedArrayTable m ℕ) :
    (FixedArrayTable m ℕ × ℕ) × ℕ :=
  let result := PaperIndexedArrayConstruction.run index (if bits then arrayWord W m else W) (element price W shift queries)
  ((result.1,54*m+18),result.2+annotation price m+64*W)

theorem data {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W shift : ℕ) (queries : FixedArrayTable m ℕ) :
    (run bits index price W shift queries).1=GeneralPaperCDFPairPlan.shiftCuts shift queries := by
  apply Prod.ext
  · unfold run GeneralPaperCDFPairPlan.shiftCuts
    dsimp only
    rw [PaperIndexedArrayConstruction.run_data,PaperIndexedArrayConstruction.run_data]
    rfl
  · exact (GeneralPaperCDFPairPlan.shift_work shift queries).symm

theorem cuts {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U shift : ℕ) (queries : FixedArrayTable m ℕ)
    (hShift : shift≤1) (hQueries : ∀ q,queries.read q<U) (q : Fin m) :
    (run bits index price W shift queries).1.1.read q≤U := by
  rw [data,GeneralPaperCDFPairPlan.shift_read]
  have h := hQueries q
  omega

theorem annotation_work (price : ℕ → ℕ) (hMono : Monotone price) (m U : ℕ) : annotation price m≤4*price (width m U) := by
  have hW := GeneralPaperSignedCutOperands.word_bound m U
  have p (op : ℕ → ℕ → ℕ) (a b : ℕ) (ha : a≤magnitude m U) (hb : b≤magnitude m U) (hc : op a b≤magnitude m U) :
      GeneralPaperNaturalPrimitivePrice.binary price op a b≤2*price (width m U) :=
    (GeneralPaperNaturalPrimitivePrice.binary_le price hMono op a b (magnitude m U) ha hb hc).trans
      (Nat.mul_le_mul_left 2 (hMono hW))
  have ha := p (fun a b => a*b) 54 m (by unfold magnitude; omega) (by unfold magnitude; omega) (by unfold magnitude; omega)
  have hb := p (fun a b => a+b) (54*m) 18 (by unfold magnitude; omega) (by unfold magnitude; omega) (by unfold magnitude; omega)
  unfold annotation
  omega

theorem element_work {m : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W U shift : ℕ) (queries : FixedArrayTable m ℕ)
    (hShift : shift≤1) (hQueries : ∀ q,queries.read q<U) (q : Fin m) :
    (element price W shift queries q).2≤2*price (width m U)+32*W := by
  have hQ := hQueries q
  have h := (GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a+b) (queries.read q) shift (magnitude m U)
    (by unfold magnitude; omega) (by unfold magnitude; omega) (by unfold magnitude; omega)).trans
      (Nat.mul_le_mul_left 2 (hMono (GeneralPaperSignedCutOperands.word_bound m U)))
  exact Nat.add_le_add_right h _

def profile (price : ℕ → ℕ) (W m U : ℕ) : ℕ :=
  m*(2*price (width m U)+32*W)+44*(m+1)*arrayWord W m+4*price (width m U)+64*W

def arithmeticProfile (m : ℕ) : ℕ := m*34+44*(m+1)+68

theorem bit_work {m : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W U shift : ℕ) (queries : FixedArrayTable m ℕ)
    (hShift : shift≤1) (hQueries : ∀ q,queries.read q<U) :
    (run true (fun w => w) price W shift queries).2≤profile price W m U := by
  have hA := GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W m) (2*price (width m U)+32*W)
    (element price W shift queries) (GeneralPaperSummaryArrayControls.array_word_positive W m)
    (GeneralPaperSummaryArrayControls.array_index W m) (element_work price hMono W U shift queries hShift hQueries)
  exact Nat.add_le_add_right (Nat.add_le_add hA (annotation_work price hMono m U)) _

theorem arithmetic_work {m : ℕ} (shift : ℕ) (queries : FixedArrayTable m ℕ) :
    (run false (fun _ => 1) (fun _ => 1) 1 shift queries).2≤arithmeticProfile m := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 34
    (element (fun _ => 1) 1 shift queries) (Nat.le_refl _) (fun _ _ => Nat.le_refl _) (fun _ => Nat.le_refl _)
  change (PaperIndexedArrayConstruction.run (fun _ => 1) 1 (element (fun _ => 1) 1 shift queries)).2+4+64≤_
  unfold arithmeticProfile
  omega

theorem every_prefix {m : ℕ} (index price : ℕ → ℕ) (W A shift : ℕ) (queries : FixedArrayTable m ℕ)
    (count : ℕ) (hCount : count≤m) :
    (PaperIndexedArrayConstruction.fill index A (element price W shift queries) count hCount).1.size=count := by
  rw [PaperIndexedArrayConstruction.fill_data,Array.size_ofFn]

end Blotto.GeneralPaperCDFShiftPrice
