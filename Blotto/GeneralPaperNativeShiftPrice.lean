import Blotto.GeneralPaperNativeShiftExecution

/-! Full operand-sensitive selected-shift prices. Constructed operands
have width O(word D+word S); adaptive work is O(word D), independent of
the numerical fuel D+1. The real path executes only arithmetic/comparisons. -/
namespace Blotto.GeneralPaperNativeShiftPrice
open GeneralPaperNativeShiftExecution
set_option autoImplicit false
set_option maxHeartbeats 3500000

def magnitude (D S : ℕ) : ℕ := 4*(S+1)*(D+1)
def width (D S : ℕ) : ℕ := 1+binaryWordWidth (magnitude D S)

theorem magnitude_bounds (D S l t : ℕ) (hD : 0<D) (_hS : 0<S) (hl : l<S) (ht : t<D) :
    2*((2*l+1)*D+1)≤magnitude D S ∧ 2*S≤magnitude D S ∧
      D+1≤magnitude D S ∧ 2*l+1≤magnitude D S ∧ 2*t+1≤magnitude D S := by
  have hn := numerator_bound D S l hD hl
  unfold magnitude
  constructor
  · nlinarith only [hn,Nat.zero_le (S*D)]
  · constructor
    · nlinarith only [Nat.zero_le (S*D),hD]
    · constructor
      · nlinarith only [Nat.zero_le (S*D),_hS]
      · constructor <;> nlinarith only [hl,ht,Nat.zero_le (S*D),hD,_hS]

theorem fixed_bound (price : ℕ → ℕ) (hMono : Monotone price) (D S l t : ℕ)
    (hD : 0<D) (hS : 0<S) (hl : l<S) (ht : t<D) : fixedCost price D S l t≤14*price (width D S) := by
  have hb := magnitude_bounds D S l t hD hS hl ht
  have hm : 2≤magnitude D S := by have h := hb.2.2.1;omega
  have hc := GeneralPaperNaturalPrimitivePrice.binary_le price hMono
  have h1 := hc (fun a b => a*b) 2 l (magnitude D S) hm (by omega) (by omega)
  have h2 := hc (fun a b => a+b) (2*l) 1 (magnitude D S) (by omega) (by omega) hb.2.2.2.1
  have h3 := hc (fun a b => a*b) (2*l+1) D (magnitude D S) hb.2.2.2.1 (by omega) (by omega)
  have h4 := hc (fun a b => a*b) 2 S (magnitude D S) hm (by omega) hb.2.1
  have h5 := hc (fun a b => a+b) D 1 (magnitude D S) (by omega) (by omega) hb.2.2.1
  have h6 := hc (fun a b => a*b) 2 t (magnitude D S) hm (by omega) (by omega)
  have h7 := hc (fun a b => a+b) (2*t) 1 (magnitude D S) (by omega) (by omega) hb.2.2.2.2
  unfold fixedCost width
  omega

theorem depth_bound (bits : Bool) (model : RationalCostModel) (W D S l : ℕ)
    (hD : 0<D) (hS : 0<S) (hl : l<S) :
    (GeneralPaperGrowingQuotientBits.run (if bits then model.rat else fun _ => 1) W ((2*l+1)*D) (2*S) (D+1)).1.depth≤binaryWordWidth D := by
  have hd := GeneralPaperGrowingQuotient.depth_word_bound (((2*l+1)*D:ℕ):ℚ) (2*S:ℚ)
    (by positivity) (D+1) (by positivity) (by exact_mod_cast fuel_cap D S l hD hS hl)
  have he := congrArg GeneralPaperGrowingQuotient.Result.depth
    (GeneralPaperNaturalGrowingQuotient.data ((2*l+1)*D) (2*S) (D+1))
  have hq := congrArg GeneralPaperGrowingQuotient.Result.quotient
    (GeneralPaperNaturalGrowingQuotient.data ((2*l+1)*D) (2*S) (D+1))
  dsimp only [GeneralPaperNaturalGrowingQuotient.lift] at he hq
  have hc : (GeneralPaperNaturalGrowingQuotient.run ((2*l+1)*D) (2*S) (D+1)).quotient=(run bits model W D S l).1.cell := by
    unfold run
    dsimp only
    rw [GeneralPaperGrowingQuotientBits.data]
  have hDouble : ((2*S:ℕ):ℚ)=2*(S:ℚ) := by push_cast;rfl
  rw [←hDouble,←he,←hq,hc] at hd
  rw [GeneralPaperGrowingQuotientBits.data]
  exact hd.trans (binaryWordWidth_mono (cell_bound bits model W D S l hD hS hl).le)

def profile (bits : Bool) (model : RationalCostModel) (W D S : ℕ) : ℕ :=
  512*(binaryWordWidth D+1)*(W+if bits then model.rat (width D S) else 1)

theorem work_bound (bits : Bool) (model : RationalCostModel) (W D S l : ℕ)
    (hD : 0<D) (hS : 0<S) (hl : l<S) : (run bits model W D S l).2≤profile bits model W D S := by
  let price := if bits then model.rat else fun _ => 1
  have hMono : Monotone price := by
    cases bits
    · exact fun _ _ _ => le_rfl
    · exact model.monotone
  have ht := cell_bound bits model W D S l hD hS hl
  have hFixed := fixed_bound price hMono D S l (run bits model W D S l).1.cell hD hS hl ht
  have hMag := magnitude_bounds D S l (run bits model W D S l).1.cell hD hS hl ht
  have hDiv := GeneralPaperGrowingQuotientBits.bounded_work price hMono W ((2*l+1)*D) (2*S) (D+1)
    (magnitude D S) (by omega) hMag.1 hMag.2.1
  have hDepth := depth_bound bits model W D S l hD hS hl
  change _≤256*((GeneralPaperGrowingQuotientBits.run price W ((2*l+1)*D) (2*S) (D+1)).1.depth+1)*
    (W+price (width D S)) at hDiv
  have hDiv' := hDiv.trans (Nat.mul_le_mul_right (W+price (width D S)) (Nat.mul_le_mul_left 256 (Nat.add_le_add_right hDepth 1)))
  change (GeneralPaperGrowingQuotientBits.run price W ((2*l+1)*D) (2*S) (D+1)).2+
    fixedCost price D S l (run bits model W D S l).1.cell+128*W≤_
  have hp : profile bits model W D S=512*(binaryWordWidth D+1)*(W+price (width D S)) := by cases bits <;> rfl
  rw [hp]
  have hPos : 1≤binaryWordWidth D+1 := by omega
  nlinarith only [hDiv',hFixed,hPos,Nat.zero_le (W*binaryWordWidth D),Nat.zero_le (price (width D S)*binaryWordWidth D)]

theorem width_bound (D S : ℕ) : width D S≤binaryWordWidth D+binaryWordWidth S+8 := by
  have hD := GeneralPaperRayOperandWidthEnvelope.word_add D 1
  have hS := GeneralPaperRayOperandWidthEnvelope.word_add S 1
  have h1 := binaryWordWidth_mul 4 (S+1)
  have h2 := binaryWordWidth_mul (4*(S+1)) (D+1)
  have hOne : binaryWordWidth 1=1 := by decide
  have hFour : binaryWordWidth 4=3 := by decide
  unfold width magnitude
  omega

theorem arithmetic_work (model : RationalCostModel) (D S l : ℕ) (hD : 0<D) (hS : 0<S) (hl : l<S) :
    (run false model 1 D S l).2≤1024*(binaryWordWidth D+1) := by
  have h := work_bound false model 1 D S l hD hS hl
  simp only [profile,Bool.false_eq_true,ite_false] at h
  nlinarith only [h]

end Blotto.GeneralPaperNativeShiftPrice
