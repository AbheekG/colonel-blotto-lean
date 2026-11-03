import Blotto.GeneralPaperAffineStepPrice

/-! Price the actual guarded pair crossing: original-slope equality, two
coefficient subtractions, negation and division. Parallel pairs execute no
division. All reduced intermediate/result words fit one root envelope.
-/
namespace Blotto.GeneralPaperAffineCrossingPrice
open GeneralPaperRayAffine GeneralPaperRayAffineComparison GeneralPaperRationalPrimitivePrice
set_option autoImplicit false
set_option maxHeartbeats 4000000

def run (primitive : ℕ → ℕ) (W : ℕ) (a b : Affine) : Option ℚ × ℕ :=
  let equality := primitive (RationalExpression.pairWidth a.slope b.slope)
  if a.slope=b.slope then (none,16*W+equality) else
    let d := difference a b
    (some d.crossing,64*W+equality+binary primitive (·-·) a.intercept b.intercept+
      binary primitive (·-·) a.slope b.slope+unary primitive Neg.neg d.intercept+
      binary primitive (·/·) (-d.intercept) d.slope)

theorem data (primitive : ℕ → ℕ) (W : ℕ) (a b : Affine) :
    (run primitive W a b).1=GeneralPaperRayCrossingPairs.crossing a b := by
  simp only [run,GeneralPaperRayCrossingPairs.crossing]
  split <;> rfl

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W D E A B R : ℕ)
    (hD : 0<D) (hE : 0<E) (hR : GeneralPaperRayAffineBound.rootWidth D E (A+A) (B+B)≤R)
    (a b : Affine) (ha : GeneralPaperRayAffineBound.Bounded D E A B a)
    (hb : GeneralPaperRayAffineBound.Bounded D E A B b) :
    (run primitive W a b).2≤64*W+9*primitive (1+2*R) := by
  have hBase := (GeneralPaperRayAffineBound.rootWidth_mono D E A B (A+A) (B+B)
    (Nat.le_add_right _ _) (Nat.le_add_right _ _)).trans hR
  have hA := GeneralPaperAffineValuePrice.coefficients hD hE a ha
  have hB := GeneralPaperAffineValuePrice.coefficients hD hE b hb
  have hAI := hA.1.mono hBase
  have hAS := hA.2.mono hBase
  have hBI := hB.1.mono hBase
  have hBS := hB.2.mono hBase
  have hd := GeneralPaperRayAffineBound.difference ha hb
  have hDiff := GeneralPaperAffineValuePrice.coefficients hD hE (difference a b) hd
  have hDI := hDiff.1.mono hR
  have hDS := hDiff.2.mono hR
  have hRoot := (GeneralPaperRayAffineBound.crossing_height hD hE hd).mono hR
  have hEq := hMono (max_le (rationalWordWidth_of_height hAS) (rationalWordWidth_of_height hBS))
  change primitive (RationalExpression.pairWidth a.slope b.slope)≤primitive (1+2*R) at hEq
  have hi := binary_le primitive hMono (·-·) a.intercept b.intercept (1+2*R)
    (rationalWordWidth_of_height hAI) (rationalWordWidth_of_height hBI) (rationalWordWidth_of_height hDI)
  have hs := binary_le primitive hMono (·-·) a.slope b.slope (1+2*R)
    (rationalWordWidth_of_height hAS) (rationalWordWidth_of_height hBS) (rationalWordWidth_of_height hDS)
  have hn := unary_le primitive hMono Neg.neg (difference a b).intercept (1+2*R)
    (rationalWordWidth_of_height hDI) (rationalWordWidth_of_height hDI.neg)
  have hv := binary_le primitive hMono (·/·) (-(difference a b).intercept) (difference a b).slope (1+2*R)
    (rationalWordWidth_of_height hDI.neg) (rationalWordWidth_of_height hDS) (rationalWordWidth_of_height hRoot)
  rw [run]
  split <;> dsimp only
  · omega
  · omega

def optionalRun (primitive : ℕ → ℕ) (W : ℕ) : Option Affine → Option Affine → Option ℚ × ℕ
  | some a,some b =>
    let crossing := run primitive W a b
    (crossing.1,crossing.2+8*W)
  | _,_ => (none,8*W)

theorem optional_data (primitive : ℕ → ℕ) (W : ℕ) (a b : Option Affine) :
    (optionalRun primitive W a b).1=GeneralPaperRayCrossingPairs.optional a b := by
  cases a <;> cases b <;> simp only [optionalRun,GeneralPaperRayCrossingPairs.optional,data]

theorem optional_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W D E A B R : ℕ)
    (hD : 0<D) (hE : 0<E) (hR : GeneralPaperRayAffineBound.rootWidth D E (A+A) (B+B)≤R)
    (a b : Option Affine)
    (ha : ∀ f,a=some f → GeneralPaperRayAffineBound.Bounded D E A B f)
    (hb : ∀ f,b=some f → GeneralPaperRayAffineBound.Bounded D E A B f) :
    (optionalRun primitive W a b).2≤72*W+9*primitive (1+2*R) := by
  cases a with
  | none => cases b <;> simp only [optionalRun] <;> omega
  | some a =>
    cases b with
    | none => simp only [optionalRun]; omega
    | some b =>
      have hh := work primitive hMono W D E A B R hD hE hR a b (ha a rfl) (hb b rfl)
      change (run primitive W a b).2+8*W≤_
      omega

end Blotto.GeneralPaperAffineCrossingPrice
