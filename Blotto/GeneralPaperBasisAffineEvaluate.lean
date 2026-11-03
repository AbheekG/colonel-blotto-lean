import Blotto.GeneralPaperBasisAffineOriginal

/-! Native evaluation at an explicit rational threshold. Its common
denominator is denominator(gamma)*D: the initializer N is absent.
-/
namespace Blotto.GeneralPaperBasisAffineEvaluate
open GeneralPaperBasisStoredProducts GeneralPaperBasisAffineData GeneralPaperBasisAffineSystem
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run {d : ℕ} (data : Data d) (numerator : ℤ) (denominator : ℕ) : GeneralPaperBasisRationalSolve.RatVector d × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 0) 1 (fun k =>
    (((((denominator:ℤ)*data.constant.read k+numerator*data.slope.read k:ℤ):ℚ)/
      (((denominator:ℤ)*data.determinant:ℤ):ℚ)),20))

theorem read {d : ℕ} (data : Data d) (numerator : ℤ) (denominator : ℕ) (k : Fin d) :
    (run data numerator denominator).1.read k=
      (((denominator:ℤ)*data.constant.read k+numerator*data.slope.read k:ℤ):ℚ)/
        (((denominator:ℤ)*data.determinant:ℤ):ℚ) := by
  simp only [run,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]

theorem real_value {d : ℕ} (data : Data d) (hD : data.determinant≠0) (numerator : ℤ)
    (denominator : ℕ) (hDen : 0<denominator) (k : Fin d) :
    ((run data numerator denominator).1.read k:ℝ)=value data ((numerator:ℝ)/(denominator:ℝ)) k := by
  have hd : (data.determinant:ℝ)≠0 := by exact_mod_cast hD
  have hn : (denominator:ℝ)≠0 := by exact_mod_cast hDen.ne'
  rw [read]
  push_cast
  unfold value
  field_simp

theorem lattice {d : ℕ} (data : Data d) (hD : data.determinant≠0) (numerator : ℤ)
    (denominator : ℕ) (hDen : 0<denominator) (k : Fin d) :
    OnRationalLattice (denominator*data.determinant.natAbs) ((run data numerator denominator).1.read k) := by
  rw [read]
  have hn : (denominator:ℤ)≠0 := by exact_mod_cast hDen.ne'
  have hh := FinitePolytopeRationalWitness.denominator_divInt
    (numerator := (denominator:ℤ)*data.constant.read k+numerator*data.slope.read k)
    (denominator := (denominator:ℤ)*data.determinant) (mul_ne_zero hn hD)
  simpa only [OnRationalLattice,Int.natAbs_mul,Int.natAbs_natCast] using hh

def atRational {d : ℕ} (data : Data d) (gamma : ℚ) : GeneralPaperBasisRationalSolve.RatVector d × ℕ :=
  run data gamma.num gamma.den

theorem rational_real {d : ℕ} (data : Data d) (hD : data.determinant≠0) (gamma : ℚ) (k : Fin d) :
    ((atRational data gamma).1.read k:ℝ)=value data (gamma:ℝ) k := by
  rw [atRational,real_value data hD gamma.num gamma.den gamma.den_pos k]
  have hh := congrArg (fun q : ℚ => (q:ℝ)) gamma.num_div_den
  have he : (gamma.num:ℝ)/(gamma.den:ℝ)=(gamma:ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] using hh
  rw [he]

theorem rational_lattice {d : ℕ} (data : Data d) (hD : data.determinant≠0) (gamma : ℚ) (k : Fin d) :
    OnRationalLattice (gamma.den*data.determinant.natAbs) ((atRational data gamma).1.read k) :=
  lattice data hD gamma.num gamma.den gamma.den_pos k

theorem work {d : ℕ} (data : Data d) (numerator : ℤ) (denominator : ℕ) :
    (run data numerator denominator).2≤96*(d+1) := by
  have hh := PaperIndexedArrayConstruction.run_work_bound (fun _ => 0) 0 (fun _ => by simp) 1
    (fun k : Fin d => (((((denominator:ℤ)*data.constant.read k+numerator*data.slope.read k:ℤ):ℚ)/
      (((denominator:ℤ)*data.determinant:ℤ):ℚ)),20))
  change (run data numerator denominator).2≤_ at hh
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_zero,Nat.zero_mul,Nat.add_zero] at hh
  omega

end Blotto.GeneralPaperBasisAffineEvaluate
