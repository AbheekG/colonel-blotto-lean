import Blotto.GeneralPaperSparseResidualPrice

/-! Native positive-slope crossing candidates and the streaming static
minimum. Nonpositive slopes skip division; the earlier original row wins
ties. Rational tests, negation/division and result writes are priced.
-/
namespace Blotto.GeneralPaperStaticMinimumPrice
open GeneralPaperRayAffine GeneralPaperRayMinimum GeneralPaperRationalPrimitivePrice
set_option autoImplicit false
set_option maxHeartbeats 4500000

def Height {i : Type*} (R : ℕ) (value : Option (Choice i)) : Prop :=
  ∀ c,value=some c → RationalHeight c.time R

def candidate {i : Type*} (primitive : ℕ → ℕ) (W : ℕ) (j : i) (a : Affine) : Option (Choice i) × ℕ :=
  let test := primitive (RationalExpression.pairWidth 0 a.slope)
  if 0<a.slope then
    (some ⟨j,a.crossing⟩,32*W+test+unary primitive Neg.neg a.intercept+
      binary primitive (·/·) (-a.intercept) a.slope)
  else (none,16*W+test)

theorem candidate_data {i : Type*} (primitive : ℕ → ℕ) (W : ℕ) (j : i) (a : Affine) :
    (candidate primitive W j a).1=GeneralPaperRayMinimum.candidate j a := by
  unfold candidate GeneralPaperRayMinimum.candidate
  split <;> rfl

theorem candidate_height {i : Type*} (primitive : ℕ → ℕ) (W D E A B R : ℕ)
    (hD : 0<D) (hE : 0<E) (hR : GeneralPaperRayAffineBound.rootWidth D E A B≤R)
    (j : i) (a : Affine) (ha : GeneralPaperRayAffineBound.Bounded D E A B a) :
    Height R (candidate primitive W j a).1 := by
  rw [candidate_data]
  intro chosen hc
  unfold GeneralPaperRayMinimum.candidate at hc
  split at hc
  · have he := Option.some.inj hc
    rw [←he]
    exact (GeneralPaperRayAffineBound.crossing_height hD hE ha).mono hR
  · contradiction

theorem candidate_work {i : Type*} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D E A B R : ℕ) (hD : 0<D) (hE : 0<E) (hR : GeneralPaperRayAffineBound.rootWidth D E A B≤R)
    (j : i) (a : Affine) (ha : GeneralPaperRayAffineBound.Bounded D E A B a) :
    (candidate primitive W j a).2≤32*W+5*primitive (1+2*R) := by
  have hc := GeneralPaperAffineValuePrice.coefficients hD hE a ha
  have hi := hc.1.mono hR
  have hs := hc.2.mono hR
  have hr := (GeneralPaperRayAffineBound.crossing_height hD hE ha).mono hR
  have hPos : 0<R := by
    have hd := binaryWordWidth_pos D
    unfold GeneralPaperRayAffineBound.rootWidth at hR
    omega
  have hz := GeneralPaperQuantizedHeight.zero_height R hPos
  have hp := hMono (max_le (rationalWordWidth_of_height hz) (rationalWordWidth_of_height hs))
  change primitive (RationalExpression.pairWidth 0 a.slope)≤primitive (1+2*R) at hp
  have hn := unary_le primitive hMono Neg.neg a.intercept (1+2*R)
    (rationalWordWidth_of_height hi) (rationalWordWidth_of_height hi.neg)
  have hd := binary_le primitive hMono (·/·) (-a.intercept) a.slope (1+2*R)
    (rationalWordWidth_of_height hi.neg) (rationalWordWidth_of_height hs) (rationalWordWidth_of_height hr)
  rw [candidate]
  split <;> dsimp only <;> omega

def pick {i : Type*} (primitive : ℕ → ℕ) (W : ℕ) :
    Option (Choice i) → Option (Choice i) → Option (Choice i) × ℕ
  | some a,some b => (if a.time≤b.time then some a else some b,
      8*W+primitive (RationalExpression.pairWidth a.time b.time))
  | none,b => (b,8*W)
  | a,none => (a,8*W)

theorem pick_data {i : Type*} (primitive : ℕ → ℕ) (W : ℕ) (a b : Option (Choice i)) :
    (pick primitive W a b).1=GeneralPaperRayMinimum.pick a b := by
  cases a <;> cases b <;> rfl

theorem pick_height {i : Type*} (primitive : ℕ → ℕ) (W R : ℕ) (a b : Option (Choice i))
    (ha : Height R a) (hb : Height R b) : Height R (pick primitive W a b).1 := by
  rw [pick_data]
  cases a with
  | none => exact hb
  | some a =>
    cases b with
    | none => exact ha
    | some b =>
      change Height R (if a.time≤b.time then some a else some b)
      split
      · exact ha
      · exact hb

theorem pick_work {i : Type*} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W R : ℕ) (a b : Option (Choice i)) (ha : Height R a) (hb : Height R b) :
    (pick primitive W a b).2≤8*W+primitive (1+2*R) := by
  cases a with
  | none => simp only [pick]; omega
  | some a =>
    cases b with
    | none => simp only [pick]; omega
    | some b =>
      have hp := hMono (max_le (rationalWordWidth_of_height (ha a rfl)) (rationalWordWidth_of_height (hb b rfl)))
      change primitive (RationalExpression.pairWidth a.time b.time)≤primitive (1+2*R) at hp
      change 8*W+primitive (RationalExpression.pairWidth a.time b.time)≤_
      omega

end Blotto.GeneralPaperStaticMinimumPrice
