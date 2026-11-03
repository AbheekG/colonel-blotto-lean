import Blotto.GeneralPaperOptionPlanPrice

/-! One indexed field loop materializes the optimizer's option plans from
retained summary/code/tag arrays. It reuses the common retained mesh and
prices field reads, each complete signed-tail plan and outer array writes.
-/
namespace Blotto.GeneralPaperOptionPlanFamily
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096
variable {R : Type}

def element {m K : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k U mesh : ℕ)
    (summaries : FixedArrayTable m (Summary k)) (codes : FixedArrayTable m (FixedArrayTable K ℕ))
    (tags : FixedArrayTable m (FixedArrayTable K R)) (field : Fin m) :
    GeneralPaperOrderedNativeOptionProfits.Plan R k K × ℕ :=
  let result := GeneralPaperOptionPlanPrice.run bits index primitive W k U mesh
    (summaries.read field) (codes.read field) (tags.read field)
  (result.1,result.2+48*W)

def run {m K : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k U mesh : ℕ)
    (summaries : FixedArrayTable m (Summary k)) (codes : FixedArrayTable m (FixedArrayTable K ℕ))
    (tags : FixedArrayTable m (FixedArrayTable K R)) :
    FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan R k K) × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W m else W)
    (element bits index primitive W k U mesh summaries codes tags)

def profile (primitive : ℕ → ℕ) (W m K k U : ℕ) : ℕ :=
  m*(GeneralPaperSignedTailPrice.profile primitive W K k U+112*W)+44*(m+1)*arrayWord W m

def arithmeticProfile (m K k : ℕ) : ℕ :=
  m*(GeneralPaperSignedTailPrice.arithmeticProfile K k+112)+44*(m+1)

theorem data {m K : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k U mesh : ℕ)
    (summaries : FixedArrayTable m (Summary k)) (codes : FixedArrayTable m (FixedArrayTable K ℕ))
    (tags : FixedArrayTable m (FixedArrayTable K R)) (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (run bits index primitive W k U mesh summaries codes tags).1=
      GeneralPaperOrderedNativeProfitOptimizer.plans k U summaries codes tags := by
  rw [run,PaperIndexedArrayConstruction.run_data]
  unfold GeneralPaperOrderedNativeProfitOptimizer.plans
  congr 1
  funext field
  exact GeneralPaperOptionPlanPrice.data bits index primitive W k U mesh
    (summaries.read field) (codes.read field) (tags.read field) hMesh

theorem element_work {m K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W k U mesh : ℕ)
    (summaries : FixedArrayTable m (Summary k)) (codes : FixedArrayTable m (FixedArrayTable K ℕ))
    (tags : FixedArrayTable m (FixedArrayTable K R)) (field : Fin m)
    (hCodes : ∀ i,(codes.read field).read i≤U) (hSummary : ∀ r,(summaries.read field).read r≤2*U) :
    (element true (fun w => w) primitive W k U mesh summaries codes tags field).2≤
      GeneralPaperSignedTailPrice.profile primitive W K k U+112*W := by
  have h := GeneralPaperOptionPlanPrice.bit_work primitive hMono W k U mesh (summaries.read field)
    (codes.read field) (tags.read field) hCodes hSummary
  unfold element
  dsimp only
  omega

theorem bit_work {m K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W k U mesh : ℕ)
    (summaries : FixedArrayTable m (Summary k)) (codes : FixedArrayTable m (FixedArrayTable K ℕ))
    (tags : FixedArrayTable m (FixedArrayTable K R))
    (hCodes : ∀ field i,(codes.read field).read i≤U) (hSummary : ∀ field r,(summaries.read field).read r≤2*U) :
    (run true (fun w => w) primitive W k U mesh summaries codes tags).2≤profile primitive W m K k U := by
  exact GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W m)
    (GeneralPaperSignedTailPrice.profile primitive W K k U+112*W)
    (element true (fun w => w) primitive W k U mesh summaries codes tags)
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (GeneralPaperSummaryArrayControls.array_index W m)
    (fun field => element_work primitive hMono W k U mesh summaries codes tags field (hCodes field) (hSummary field))

theorem arithmetic_work {m K : ℕ} (k U mesh : ℕ) (summaries : FixedArrayTable m (Summary k))
    (codes : FixedArrayTable m (FixedArrayTable K ℕ)) (tags : FixedArrayTable m (FixedArrayTable K R)) :
    (run false (fun _ => 1) (fun _ => 1) 1 k U mesh summaries codes tags).2≤arithmeticProfile m K k := by
  have hC (field : Fin m) :
      (element false (fun _ => 1) (fun _ => 1) 1 k U mesh summaries codes tags field).2≤
        GeneralPaperSignedTailPrice.arithmeticProfile K k+112 := by
    have h := GeneralPaperOptionPlanPrice.arithmetic_work k U mesh (summaries.read field) (codes.read field) (tags.read field)
    change _+48≤_
    omega
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1
    (GeneralPaperSignedTailPrice.arithmeticProfile K k+112)
    (element false (fun _ => 1) (fun _ => 1) 1 k U mesh summaries codes tags)
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _) hC
  simpa only [run,Bool.false_eq_true,ite_false,arithmeticProfile,Nat.mul_one] using h

theorem every_prefix {m K : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W A k U mesh : ℕ)
    (summaries : FixedArrayTable m (Summary k)) (codes : FixedArrayTable m (FixedArrayTable K ℕ))
    (tags : FixedArrayTable m (FixedArrayTable K R)) (count : ℕ) (hCount : count≤m) :
    (PaperIndexedArrayConstruction.fill index A (element bits index primitive W k U mesh summaries codes tags) count hCount).1.size=count := by
  rw [PaperIndexedArrayConstruction.fill_data,Array.size_ofFn]

end Blotto.GeneralPaperOptionPlanFamily
