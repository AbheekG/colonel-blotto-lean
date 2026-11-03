import Blotto.PlayerSpecificAlgebraicFourReflectedDraw

/-! One fresh outer midpoint coin chooses the actual uniform or reflected
small component. Both branches fit the same fixed finite-bit packet. -/
namespace Blotto.PlayerSpecificAlgebraicFourSmallDraw
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicFourInput
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def takeBits {n m : ℕ} (h : n ≤ m) (bits : Fin m → Bool) : Fin n → Bool :=
  fun j => bits ⟨j.val,lt_of_lt_of_le j.isLt h⟩

def remaining (H K : ℕ) : ℕ := (2*H)+((17*H+K)+K)
def bitCount (H K : ℕ) : ℕ := H+remaining H K

theorem uniform_bit_bound (H K : ℕ) : 8*H+K ≤ remaining H K := by unfold remaining; omega

def draw (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin (bitCount H K) → Bool) : FixedArrayTable 4 Data :=
  let rest := secondBitBlock H (remaining H K) bits
  let useUniform := PlayerSpecificAlgebraicMidpointCoin.run RationalCostModel.schoolbook r.root a.probability H
    (firstBitBlock H (remaining H K) bits)
  if useUniform then PlayerSpecificAlgebraicFourMergedDraw.draw RationalCostModel.schoolbook r.root a H K
    (takeBits (uniform_bit_bound H K) rest)
  else PlayerSpecificAlgebraicFourReflectedDraw.draw r a H K rest

theorem every_path (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T)
    (hcase : i.w < (1-i.p)*i.ell) (H K : ℕ) (bits : Fin (bitCount H K) → Bool) :
    FullBudget i.B (values (draw r a H K bits) x) := by
  unfold draw
  dsimp only
  split
  · exact PlayerSpecificAlgebraicFourMergedDraw.every_path RationalCostModel.schoolbook r.root a i
      hm hirr hv x hx ha T hfit hcase H K _
  · exact PlayerSpecificAlgebraicFourReflectedDraw.every_path r a i hm hirr hv x hx ha T hfit hml hmT hT hcase H K _

def height (T K : ℕ) : ℕ := max (PlayerSpecificAlgebraicFourMergedDraw.height T K) (PlayerSpecificAlgebraicFourReflectedDraw.height T K)
def coefficient : ℕ := PlayerSpecificAlgebraicFourMergedDraw.coefficient+PlayerSpecificAlgebraicFourReflectedDraw.coefficient

theorem max_linear (A B a b S : ℕ) (ha : a+1 ≤ A*S) (hb : b+1 ≤ B*S) : max a b+1 ≤ (A+B)*S := by
  have ha' := ha.trans (Nat.mul_le_mul_right S (by omega : A ≤ A+B))
  have hb' := hb.trans (Nat.mul_le_mul_right S (by omega : B ≤ A+B))
  omega

theorem height_linear (T K : ℕ) : height T K+1 ≤ coefficient*(T+K+1) :=
  max_linear _ _ _ _ _ (PlayerSpecificAlgebraicFourMergedDraw.height_linear T K)
    (PlayerSpecificAlgebraicFourReflectedDraw.height_linear T K)

theorem bounds (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T) (hT : 2 ≤ T)
    (hcase : i.w < (1-i.p)*i.ell) (H K : ℕ) (bits : Fin (bitCount H K) → Bool) :
    ∀ j,Reduced r.root.polynomial ((draw r a H K bits).read j) ∧ HasHeight ((draw r a H K bits).read j) (height T K) := by
  have hm0 : r.root.polynomial ≠ [] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  unfold draw
  dsimp only
  split
  · intro j
    have h := PlayerSpecificAlgebraicFourMergedDraw.bounds RationalCostModel.schoolbook r.root a T hfit hm hm0 hml hmT hT H K (takeBits (uniform_bit_bound H K) (secondBitBlock H (remaining H K) bits)) j
    exact ⟨h.1,mono h.2 (le_max_left _ _)⟩
  · intro j
    have h := PlayerSpecificAlgebraicFourReflectedDraw.bounds r a i hm hirr hv x hx ha T hfit hml hmT hT hcase H K (secondBitBlock H (remaining H K) bits) j
    exact ⟨h.1,mono h.2 (le_max_right _ _)⟩

theorem random_bit_budget (N H K : ℕ) : bitCount H K ≤ (N+1000)*H+2*K := by
  have h := Nat.mul_le_mul_right H (show 20 ≤ N+1000 by omega)
  unfold bitCount remaining
  omega

end Blotto.PlayerSpecificAlgebraicFourSmallDraw
