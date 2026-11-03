import Blotto.GeneralPaperNaturalGrowingQuotient

/-! Bit-priced adaptive arithmetic division on constructed natural inputs.
Charge each reached test, raw divisor/counter doubling, add/subtraction and
written result. The bound uses actual successful depth, never full fuel.
-/
namespace Blotto.GeneralPaperGrowingQuotientBits
open GeneralPaperIntegerWordPrice
set_option autoImplicit false
set_option maxHeartbeats 8000000

def extra (primitive : ℕ → ℕ) (a : ℕ) (higher : GeneralPaperNaturalGrowingQuotient.Result) : ℕ :=
  if a≤higher.remainder then
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (2*higher.quotient) 1+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a-b) higher.remainder a
  else primitive (1+binaryWordWidth higher.remainder)

def run (primitive : ℕ → ℕ) (W n a : ℕ) : ℕ → GeneralPaperNaturalGrowingQuotient.Result × ℕ
  | 0 => (⟨0,n,0,4⟩,16*W+primitive (1+binaryWordWidth n))
  | fuel+1 =>
    let test := compare primitive n a
    if n<a then (⟨0,n,0,4⟩,32*W+test+primitive (1+binaryWordWidth n)) else
      let higher := run primitive W n (2*a) fuel
      let result : GeneralPaperNaturalGrowingQuotient.Result :=
        if a≤higher.1.remainder then
          ⟨2*higher.1.quotient+1,higher.1.remainder-a,higher.1.depth+1,higher.1.work+14⟩
        else ⟨2*higher.1.quotient,higher.1.remainder,higher.1.depth+1,higher.1.work+14⟩
      (result,higher.2+64*W+test+
        GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 a+
        compare primitive a higher.1.remainder+
        GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 higher.1.quotient+
        extra primitive a higher.1)

theorem data (primitive : ℕ → ℕ) (W n a fuel : ℕ) :
    (run primitive W n a fuel).1=GeneralPaperNaturalGrowingQuotient.run n a fuel := by
  induction fuel generalizing a with
  | zero => rfl
  | succ fuel ih =>
    rw [run,GeneralPaperNaturalGrowingQuotient.run]
    split
    · rfl
    · dsimp only
      rw [ih (2*a)]

theorem bounded_work (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W n a fuel M : ℕ) (ha : 0<a) (hN : 2*(n+1)≤M) (hA : a≤M) :
    (run primitive W n a fuel).2≤256*((run primitive W n a fuel).1.depth+1)*
      (W+primitive (1+binaryWordWidth M)) := by
  induction fuel generalizing a with
  | zero =>
    have hn := hMono (Nat.add_le_add_left (binaryWordWidth_mono (show n≤M by omega)) 1)
    change 16*W+primitive (1+binaryWordWidth n)≤256*(0+1)*(W+primitive (1+binaryWordWidth M))
    omega
  | succ fuel ih =>
    let L := 1+binaryWordWidth M
    let P := primitive L
    have bound (x : ℕ) (hx : x≤M) : 1+binaryWordWidth x≤L :=
      Nat.add_le_add_left (binaryWordWidth_mono hx) 1
    have ht := compare_le primitive hMono n a L (bound n (by omega)) (bound a hA)
    by_cases hStop : n<a
    · rw [run,ite_eq_left hStop]
      dsimp only
      have hn := hMono (bound n (by omega))
      change 32*W+compare primitive n a+primitive (1+binaryWordWidth n)≤256*(0+1)*(W+P)
      change compare primitive n a≤P at ht
      change primitive (1+binaryWordWidth n)≤P at hn
      omega
    · have hDouble : 2*a≤M := by omega
      have hi := ih (2*a) (by omega) hDouble
      have hh := GeneralPaperNaturalGrowingQuotient.operand_bounds n (2*a) fuel (by omega)
      have hq : (run primitive W n (2*a) fuel).1.quotient≤n := by rw [data]; exact hh.1
      have hr : (run primitive W n (2*a) fuel).1.remainder≤n := by rw [data]; exact hh.2.1
      have hd := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a*b) 2 a M (by omega) hA hDouble
      have hc := compare_le primitive hMono a (run primitive W n (2*a) fuel).1.remainder L
        (bound a hA) (bound _ (by omega))
      have hqCost := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a*b)
        2 (run primitive W n (2*a) fuel).1.quotient M (by omega) (by omega) (by omega)
      have he : extra primitive a (run primitive W n (2*a) fuel).1≤4*P := by
        unfold extra
        split
        · have hAdd := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a+b)
            (2*(run primitive W n (2*a) fuel).1.quotient) 1 M (by omega) (by omega) (by omega)
          have hSub := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a-b)
            (run primitive W n (2*a) fuel).1.remainder a M (by omega) hA (by omega)
          change _≤2*P at hAdd hSub
          omega
        · exact (hMono (bound _ (by omega))).trans (by omega)
      rw [run,ite_eq_right hStop]
      dsimp only
      change (run primitive W n (2*a) fuel).2+64*W+compare primitive n a+
        GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 a+
        compare primitive a (run primitive W n (2*a) fuel).1.remainder+
        GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 (run primitive W n (2*a) fuel).1.quotient+
        extra primitive a (run primitive W n (2*a) fuel).1≤_
      change _≤256*((run primitive W n (2*a) fuel).1.depth+1)*(W+P) at hi
      change compare primitive n a≤P at ht
      change compare primitive a (run primitive W n (2*a) fuel).1.remainder≤P at hc
      change _≤2*P at hd hqCost
      split <;> dsimp only <;> nlinarith only [hi,ht,hd,hc,hqCost,he]

def width (n a : ℕ) : ℕ := 16+4*binaryWordWidth n+4*binaryWordWidth a

theorem magnitude_width (n a : ℕ) : 1+binaryWordWidth (2*(n+a+1))≤width n a := by
  have hA := GeneralPaperRayOperandWidthEnvelope.word_add n a
  have hB := GeneralPaperRayOperandWidthEnvelope.word_add (n+a) 1
  have hC := binaryWordWidth_mul 2 (n+a+1)
  have h1 : binaryWordWidth 1=1 := by decide
  have h2 : binaryWordWidth 2=2 := by decide
  unfold width
  omega

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W n a fuel : ℕ) (ha : 0<a) :
    (run primitive W n a fuel).2≤256*((GeneralPaperGrowingQuotient.run (n:ℚ) (a:ℚ) fuel).depth+1)*
      (W+primitive (width n a)) := by
  have hh := bounded_work primitive hMono W n a fuel (2*(n+a+1)) ha (by omega) (by omega)
  rw [data] at hh
  have hd := congrArg GeneralPaperGrowingQuotient.Result.depth (GeneralPaperNaturalGrowingQuotient.data n a fuel)
  dsimp only [GeneralPaperNaturalGrowingQuotient.lift] at hd
  rw [hd] at hh
  exact hh.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (hMono (magnitude_width n a)) W))

end Blotto.GeneralPaperGrowingQuotientBits
