import Blotto.GeneralPaperRetainedBasisInputs
import Blotto.GeneralPaperEndpointRecheckWork

/-! Evaluate with constructed, possibly unreduced integer numerator and
positive natural denominator. No rational encoding is recovered on the
data path. Every integer operation, cast, rational division, array write
and index/control step has its declared paper-model price. -/
namespace Blotto.GeneralPaperRawAffineEvaluate
open GeneralPaperBasisAffineData GeneralPaperSourceRowsExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

def entry {d : ℕ} (primitive : ℕ → ℕ) (A : ℕ) (data : Data d)
    (numerator : ℤ) (denominator : ℕ) (k : Fin d) : ℚ×ℕ :=
  let n : ℤ := denominator
  let c := data.constant.read k
  let s := data.slope.read k
  let a := n*c
  let b := numerator*s
  let top := a+b
  let bottom := n*data.determinant
  (((top:ℤ):ℚ)/((bottom:ℤ):ℚ),
    GeneralPaperIntegerPrimitivePrice.binary primitive (fun x y => x*y) n c+
    GeneralPaperIntegerPrimitivePrice.binary primitive (fun x y => x*y) numerator s+
    GeneralPaperIntegerPrimitivePrice.binary primitive (fun x y => x+y) a b+
    GeneralPaperIntegerPrimitivePrice.binary primitive (fun x y => x*y) n data.determinant+
    primitive (GeneralPaperIntegerPrimitivePrice.word n)+
    primitive (GeneralPaperIntegerPrimitivePrice.word top)+
    primitive (GeneralPaperIntegerPrimitivePrice.word bottom)+
    primitive (rationalWordWidth (top:ℚ))+primitive (rationalWordWidth (bottom:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary primitive (fun x y => x/y) (top:ℚ) (bottom:ℚ)+16*A)

def run {d : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (data : Data d)
    (numerator : ℤ) (denominator : ℕ) : GeneralPaperBasisRationalSolve.RatVector d×ℕ :=
  let P := if bits then model.rat else fun _ => 1
  let A := if bits then W else 1
  let result := PaperIndexedArrayConstruction.run (if bits then (fun w => w) else fun _ => 1) A
    (entry P A data numerator denominator)
  (result.1,result.2+P (1+binaryWordWidth denominator)+16*A)

theorem data {d : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (cache : Data d)
    (numerator : ℤ) (denominator : ℕ) :
    (run bits model W cache numerator denominator).1=
      (GeneralPaperBasisAffineEvaluate.run cache numerator denominator).1 := by
  simp only [run,GeneralPaperBasisAffineEvaluate.run,PaperIndexedArrayConstruction.run_data,entry]

theorem coordinate {d : ℕ} (cache : Data d) (numerator : ℤ) (denominator : ℕ)
    (hDen : 0<denominator) (k : Fin d) :
    (GeneralPaperBasisAffineEvaluate.run cache numerator denominator).1.read k=
      ((cache.constant.read k:ℚ)+((numerator:ℚ)/(denominator:ℚ))*(cache.slope.read k:ℚ))/(cache.determinant:ℚ) := by
  have hn : (denominator:ℚ)≠0 := by exact_mod_cast hDen.ne'
  rw [GeneralPaperBasisAffineEvaluate.read]
  push_cast
  by_cases hd : (cache.determinant:ℚ)=0
  · simp only [hd,mul_zero,div_zero]
  · field_simp

theorem represented {d : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (cache : Data d)
    (numerator : ℤ) (denominator : ℕ) (hDen : 0<denominator) (gamma : ℚ)
    (hGamma : (numerator:ℚ)/(denominator:ℚ)=gamma) :
    (run bits model W cache numerator denominator).1=(GeneralPaperBasisAffineEvaluate.atRational cache gamma).1 := by
  rw [data]
  have hh : ∀ k : Fin d,
      (GeneralPaperBasisAffineEvaluate.run cache numerator denominator).1.read k=
      (GeneralPaperBasisAffineEvaluate.run cache gamma.num gamma.den).1.read k := by
    intro k
    rw [coordinate cache numerator denominator hDen k,coordinate cache gamma.num gamma.den gamma.den_pos k,
      hGamma,gamma.num_div_den]
  simp only [GeneralPaperBasisAffineEvaluate.run,PaperIndexedArrayConstruction.run_data,
    FixedArrayTable.read_ofFn] at hh
  simp only [GeneralPaperBasisAffineEvaluate.atRational,GeneralPaperBasisAffineEvaluate.run,
    PaperIndexedArrayConstruction.run_data]
  congr 1
  funext k
  exact hh k

theorem arithmetic_work {d : ℕ} (model : RationalCostModel) (cache : Data d)
    (numerator : ℤ) (denominator : ℕ) :
    (run false model 1 cache numerator denominator).2≤128*(d+1) := by
  have hh := PaperIndexedArrayConstruction.run_work (fun _ => 1) 1 (entry (fun _ => 1) 1 cache numerator denominator)
  have ho := GeneralPaperUnitArrayOverhead.overhead 1 d d
  simp only [entry,GeneralPaperIntegerPrimitivePrice.binary,GeneralPaperRationalPrimitivePrice.binary,
    Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hh
  change (PaperIndexedArrayConstruction.run (fun _ => 1) 1 (entry (fun _ => 1) 1 cache numerator denominator)).2+17≤128*(d+1)
  omega

end Blotto.GeneralPaperRawAffineEvaluate
