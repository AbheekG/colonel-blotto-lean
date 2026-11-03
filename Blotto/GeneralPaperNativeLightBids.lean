import Blotto.GeneralPaperCircleRationalCoefficients

/-! Native rational light-bid output from stored sorted references and
the returned sweep indices. Each product and written rational is priced.
The total fallback for an invalid index is unreachable in the joined draw. -/
namespace Blotto.GeneralPaperNativeLightBids
set_option autoImplicit false
set_option maxHeartbeats 1800000

def read {R : ℕ} (hR : 0<R) (sorted : FixedArrayTable R ℚ) (a : ℕ) : ℚ :=
  if h:a<R then sorted.read ⟨a,h⟩ else sorted.read ⟨0,hR⟩

theorem read_valid {R : ℕ} (hR : 0<R) (sorted : FixedArrayTable R ℚ) (a : Fin R) : read hR sorted a.val=sorted.read a := by
  rw [read,dite_eq_left a.isLt]

def coordinate {R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hR : 0<R)
    (sorted : FixedArrayTable R ℚ) (coefficient : ℚ) (a : ℕ) : ℚ × ℕ :=
  let x := read hR sorted a
  (coefficient*x,GeneralPaperRationalPrimitivePrice.binary price (fun a b => a*b) coefficient x+
    8*index (binaryWordWidth (a+1))+8*index (binaryWordWidth (R+1))+64*A)

def run {g R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hR : 0<R)
    (coefficients : FixedArrayTable g ℚ) (sorted : FixedArrayTable R ℚ) (chosen : FixedArrayTable g ℕ) : FixedArrayTable g ℚ × ℕ :=
  PaperIndexedArrayConstruction.run index A (fun j => coordinate price index A hR sorted (coefficients.read j) (chosen.read j))

theorem data {g R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hR : 0<R)
    (coefficients : FixedArrayTable g ℚ) (sorted : FixedArrayTable R ℚ) (chosen : FixedArrayTable g ℕ) :
    (run price index A hR coefficients sorted chosen).1=
      FixedArrayTable.ofFn (fun j => coefficients.read j*read hR sorted (chosen.read j)) := by
  unfold run
  rw [PaperIndexedArrayConstruction.run_data]
  rfl

theorem coordinate_height {R : ℕ} (hR : 0<R) (sorted : FixedArrayTable R ℚ) (c : ℚ) (a C H : ℕ)
    (hc : RationalHeight c C) (hs : ∀ j,RationalHeight (sorted.read j) H) : RationalHeight (c*read hR sorted a) (C+H) := by
  unfold read
  split_ifs <;> exact hc.mul (hs _)

theorem height {g R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (hR : 0<R)
    (coefficients : FixedArrayTable g ℚ) (sorted : FixedArrayTable R ℚ) (chosen : FixedArrayTable g ℕ) (C H : ℕ)
    (hc : ∀ j,RationalHeight (coefficients.read j) C) (hs : ∀ a,RationalHeight (sorted.read a) H) (j : Fin g) :
    RationalHeight ((run price index A hR coefficients sorted chosen).1.read j) (C+H) := by
  rw [data,FixedArrayTable.read_ofFn]
  exact coordinate_height hR sorted _ _ C H (hc j) hs

theorem coordinate_work {R : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A C H : ℕ) (hR : 0<R)
    (sorted : FixedArrayTable R ℚ) (c : ℚ) (a : ℕ) (ha : a<R) (hc : RationalHeight c C)
    (hs : ∀ j,RationalHeight (sorted.read j) H) (hIndex : ∀ i≤R,index (binaryWordWidth (i+1))≤A) :
    (coordinate price index A hR sorted c a).2≤2*price (1+2*(C+H))+80*A := by
  have hRead : RationalHeight (read hR sorted a) H := by unfold read; (split_ifs; exact hs _)
  have hMul := GeneralPaperRationalPrimitivePrice.binary_le price hMono (fun a b => a*b) c (read hR sorted a)
    (1+2*(C+H)) ((rationalWordWidth_of_height hc).trans (by omega))
    ((rationalWordWidth_of_height hRead).trans (by omega)) (rationalWordWidth_of_height (hc.mul hRead))
  have hA := hIndex a ha.le
  have hR' := hIndex R le_rfl
  unfold coordinate
  dsimp only
  omega

theorem work {g R : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A C H : ℕ) (hA : 1≤A) (hR : 0<R)
    (coefficients : FixedArrayTable g ℚ) (sorted : FixedArrayTable R ℚ) (chosen : FixedArrayTable g ℕ)
    (hc : ∀ j,RationalHeight (coefficients.read j) C) (hs : ∀ a,RationalHeight (sorted.read a) H)
    (hChosen : ∀ j,chosen.read j<R) (hIndexG : ∀ i≤g,index (binaryWordWidth (i+1))≤A)
    (hIndexR : ∀ i≤R,index (binaryWordWidth (i+1))≤A) :
    (run price index A hR coefficients sorted chosen).2≤
      g*(2*price (1+2*(C+H))+80*A)+44*(g+1)*A :=
  GeneralPaperControlArrayPrice.indexed_work index A _ _ hA hIndexG
    (fun j => coordinate_work price index hMono A C H hR sorted _ _ (hChosen j) (hc j) hs hIndexR)

end Blotto.GeneralPaperNativeLightBids
