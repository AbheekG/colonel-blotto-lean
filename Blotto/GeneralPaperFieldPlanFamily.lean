import Blotto.GeneralPaperFieldPlanPreparation

/-! One indexed field loop consumes the four retained summary families and
two retained option-code families. All six field reads and array control,
reference writes and allocations are priced; every prefix has its true size.
-/
namespace Blotto.GeneralPaperFieldPlanFamily
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def element {m mx my : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ)
    (p q lambda mu : FixedArrayTable m (Summary k))
    (candidateOptions : FixedArrayTable m (FixedArrayTable mx ℕ)) (responseOptions : FixedArrayTable m (FixedArrayTable my ℕ))
    (field : Fin m) : GeneralPaperEpochFieldPlan.Plan k × ℕ :=
  let result := GeneralPaperFieldPlanPreparation.run bits index price W k U
    (p.read field) (q.read field) (lambda.read field) (mu.read field) (candidateOptions.read field) (responseOptions.read field)
  (result.1,result.2+96*W)

def run {m mx my : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ)
    (p q lambda mu : FixedArrayTable m (Summary k))
    (candidateOptions : FixedArrayTable m (FixedArrayTable mx ℕ)) (responseOptions : FixedArrayTable m (FixedArrayTable my ℕ)) :
    FixedArrayTable m (GeneralPaperEpochFieldPlan.Plan k) × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W m else W)
    (element bits index price W k U p q lambda mu candidateOptions responseOptions)

def profile (price : ℕ → ℕ) (W m mx my k U : ℕ) : ℕ :=
  m*(GeneralPaperFieldPlanPreparation.profile price W mx my k U+96*W)+44*(m+1)*arrayWord W m

def arithmeticProfile (m mx my k : ℕ) : ℕ :=
  m*(GeneralPaperFieldPlanPreparation.arithmeticProfile mx my k+96)+44*(m+1)

theorem data {m mx my : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ)
    (p q lambda mu : FixedArrayTable m (Summary k))
    (candidateOptions : FixedArrayTable m (FixedArrayTable mx ℕ)) (responseOptions : FixedArrayTable m (FixedArrayTable my ℕ)) :
    (run bits index price W k U p q lambda mu candidateOptions responseOptions).1=
      FixedArrayTable.ofFn (fun j => GeneralPaperEpochFieldPlan.prepare k U
        (p.read j) (q.read j) (lambda.read j) (mu.read j) (candidateOptions.read j) (responseOptions.read j)) := by
  rw [run,PaperIndexedArrayConstruction.run_data]
  congr 1
  funext j
  exact GeneralPaperFieldPlanPreparation.data bits index price W k U _ _ _ _ _ _

theorem bit_work {m mx my : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W k U : ℕ) (p q lambda mu : FixedArrayTable m (Summary k))
    (candidateOptions : FixedArrayTable m (FixedArrayTable mx ℕ)) (responseOptions : FixedArrayTable m (FixedArrayTable my ℕ))
    (hp : ∀ j r,(p.read j).read r<U) (hq : ∀ j r,(q.read j).read r<U)
    (hl : ∀ j r,(lambda.read j).read r<2*U) (hm : ∀ j r,(mu.read j).read r<2*U)
    (hx : ∀ j r,(candidateOptions.read j).read r<U) (hy : ∀ j r,(responseOptions.read j).read r<U) :
    (run true (fun w => w) price W k U p q lambda mu candidateOptions responseOptions).2≤profile price W m mx my k U := by
  have hElement (j : Fin m) :
      (element true (fun w => w) price W k U p q lambda mu candidateOptions responseOptions j).2≤
        GeneralPaperFieldPlanPreparation.profile price W mx my k U+96*W :=
    Nat.add_le_add_right (GeneralPaperFieldPlanPreparation.bit_work price hMono W k U _ _ _ _ _ _
      (hp j) (hq j) (hl j) (hm j) (hx j) (hy j)) _
  exact GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W m) _
    (element true (fun w => w) price W k U p q lambda mu candidateOptions responseOptions)
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (GeneralPaperSummaryArrayControls.array_index W m) hElement

theorem arithmetic_work {m mx my : ℕ} (k U : ℕ) (p q lambda mu : FixedArrayTable m (Summary k))
    (candidateOptions : FixedArrayTable m (FixedArrayTable mx ℕ)) (responseOptions : FixedArrayTable m (FixedArrayTable my ℕ))
    (hp : ∀ j r,(p.read j).read r<U) (hq : ∀ j r,(q.read j).read r<U)
    (hl : ∀ j r,(lambda.read j).read r<2*U) (hm : ∀ j r,(mu.read j).read r<2*U)
    (hx : ∀ j r,(candidateOptions.read j).read r<U) (hy : ∀ j r,(responseOptions.read j).read r<U) :
    (run false (fun _ => 1) (fun _ => 1) 1 k U p q lambda mu candidateOptions responseOptions).2≤arithmeticProfile m mx my k := by
  have hElement (j : Fin m) :
      (element false (fun _ => 1) (fun _ => 1) 1 k U p q lambda mu candidateOptions responseOptions j).2≤
        GeneralPaperFieldPlanPreparation.arithmeticProfile mx my k+96 :=
    Nat.add_le_add_right (GeneralPaperFieldPlanPreparation.arithmetic_work k U _ _ _ _ _ _
      (hp j) (hq j) (hl j) (hm j) (hx j) (hy j)) _
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 _
    (element false (fun _ => 1) (fun _ => 1) 1 k U p q lambda mu candidateOptions responseOptions)
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _) hElement
  simpa only [run,Bool.false_eq_true,ite_false,arithmeticProfile,Nat.mul_one] using h

theorem every_prefix {m mx my : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A k U : ℕ)
    (p q lambda mu : FixedArrayTable m (Summary k))
    (candidateOptions : FixedArrayTable m (FixedArrayTable mx ℕ)) (responseOptions : FixedArrayTable m (FixedArrayTable my ℕ))
    (count : ℕ) (hCount : count≤m) :
    (PaperIndexedArrayConstruction.fill index A
      (element bits index price W k U p q lambda mu candidateOptions responseOptions) count hCount).1.size=count := by
  rw [PaperIndexedArrayConstruction.fill_data,Array.size_ofFn]

end Blotto.GeneralPaperFieldPlanFamily
