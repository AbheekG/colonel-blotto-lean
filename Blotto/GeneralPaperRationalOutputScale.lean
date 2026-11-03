import Blotto.GeneralPaperOriginalScatterLaw

/-! Final rational budget scaling and original-coordinate output writes.
The original scale's operand length is charged explicitly in every written
product; it is kept outside unit-row sorting and coefficient preparation. -/
namespace Blotto.GeneralPaperRationalOutputScale
set_option autoImplicit false
set_option maxHeartbeats 1600000

def run {n : ℕ} (price index : ℕ → ℕ) (A : ℕ) (c : ℚ) (values : FixedArrayTable n ℚ) : FixedArrayTable n ℚ × ℕ :=
  PaperIndexedArrayConstruction.run index A (fun j =>
    let x := values.read j
    (c*x,GeneralPaperRationalPrimitivePrice.binary price (fun a b => a*b) c x+64*A))

theorem data {n : ℕ} (price index : ℕ → ℕ) (A : ℕ) (c : ℚ) (values : FixedArrayTable n ℚ) :
    (run price index A c values).1=FixedArrayTable.ofFn (fun j => c*values.read j) := by
  unfold run
  rw [PaperIndexedArrayConstruction.run_data]

theorem real_data {n : ℕ} (price index : ℕ → ℕ) (A : ℕ) (c : ℚ) (values : FixedArrayTable n ℚ) :
    (fun j => ((run price index A c values).1.read j:ℝ))=scaleAllocation (c:ℝ) (fun j => (values.read j:ℝ)) := by
  funext j
  rw [data,FixedArrayTable.read_ofFn]
  simp only [scaleAllocation,Rat.cast_mul]

theorem feasible {n : ℕ} (price index : ℕ → ℕ) (A : ℕ) (c : ℚ) (hc : 0≤c) (values : FixedArrayTable n ℚ) (B : ℝ)
    (h : Feasible B (fun j => (values.read j:ℝ))) :
    Feasible ((c:ℝ)*B) (fun j => ((run price index A c values).1.read j:ℝ)) := by
  rw [real_data]
  exact scaleAllocation_feasible (by exact_mod_cast hc) h

theorem height {n : ℕ} (price index : ℕ → ℕ) (A : ℕ) (c : ℚ) (values : FixedArrayTable n ℚ) (C H : ℕ)
    (hc : RationalHeight c C) (h : ∀ j,RationalHeight (values.read j) H) (j : Fin n) :
    RationalHeight ((run price index A c values).1.read j) (C+H) := by
  rw [data,FixedArrayTable.read_ofFn]
  exact hc.mul (h j)

theorem work {n : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A C H : ℕ) (hA : 1≤A)
    (c : ℚ) (values : FixedArrayTable n ℚ) (hc : RationalHeight c C) (h : ∀ j,RationalHeight (values.read j) H)
    (hIndex : ∀ i≤n,index (binaryWordWidth (i+1))≤A) :
    (run price index A c values).2≤n*(2*price (1+2*(C+H))+64*A)+44*(n+1)*A := by
  apply GeneralPaperControlArrayPrice.indexed_work index A _ _ hA hIndex
  intro j
  have hm := GeneralPaperRationalPrimitivePrice.binary_le price hMono (fun a b => a*b) c (values.read j) (1+2*(C+H))
    ((rationalWordWidth_of_height hc).trans (by omega)) ((rationalWordWidth_of_height (h j)).trans (by omega))
    (rationalWordWidth_of_height (hc.mul (h j)))
  dsimp only
  omega

theorem models_data {n : ℕ} (price price' index index' : ℕ → ℕ) (A A' : ℕ) (c : ℚ) (values : FixedArrayTable n ℚ) :
    (run price index A c values).1=(run price' index' A' c values).1 := by rw [data,data]

theorem arithmetic_work {n : ℕ} (c : ℚ) (values : FixedArrayTable n ℚ) :
    (run (fun _ => 1) (fun _ => 1) 1 c values).2≤110*n+44 := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 66
    (fun j => (c*values.read j,GeneralPaperRationalPrimitivePrice.binary (fun _ => 1) (fun a b => a*b) c (values.read j)+64))
    (by decide) (fun _ _ => le_rfl) (by intro j; simp only [GeneralPaperRationalPrimitivePrice.binary]; decide)
  change (PaperIndexedArrayConstruction.run (fun _ => 1) 1 _).2≤_
  nlinarith only [h]

end Blotto.GeneralPaperRationalOutputScale
