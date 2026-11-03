import Blotto.GeneralPaperTreePrefix

/-! The actual scaled comparison, with its width constructed from the selected
precision and summary size. Both branch implications refer to exact full-code
masses; no monotonicity of rounded queries is assumed.
-/
namespace Blotto.GeneralPaperQuantileComparison
open GeneralPaperDyadicFloat GeneralPaperPreparedPowers GeneralPaperMassApproximation
open GeneralPaperNormalizedMassError
set_option autoImplicit false
set_option maxHeartbeats 2500000

def width (lambda k : ℕ) : ℕ := (prepare lambda k).format.fractionalBits+1+(34+k)

def choose (lambda k j : ℕ) (storedTotal storedPrefix : Number) : GeneralPaperDyadicCompare.Result :=
  GeneralPaperDyadicCompare.scaledLE (width lambda k) j storedTotal
    (GeneralPaperSourceParameters.prepare k).summarySize storedPrefix

theorem comparison_rational (w j s : ℕ) (storedPrefix storedTotal : Number) (P T e : ℚ)
    (hS : 0<s) (hT : 0<T) (hP : 0≤P) (hPT : P≤T) (he : 0≤e) (hOne : e<1)
    (hPrefix : (1-e)*P≤value storedPrefix ∧ value storedPrefix≤P)
    (hTotal : (1-e)*T≤value storedTotal ∧ value storedTotal≤T)
    (hLeft : (GeneralPaperDyadicCompare.scale j storedTotal).mantissa<2^w)
    (hRight : (GeneralPaperDyadicCompare.scale s storedPrefix).mantissa<2^w) :
    ((GeneralPaperDyadicCompare.scaledLE w j storedTotal s storedPrefix).answer=true →
      (j:ℚ)/s-2*e/(1-e)≤P/T) ∧
    ((GeneralPaperDyadicCompare.scaledLE w j storedTotal s storedPrefix).answer=false →
      P/T≤(j:ℚ)/s+2*e/(1-e)) := by
  have hp : (1-(e:ℝ))*(P:ℝ)≤(value storedPrefix:ℝ) ∧ (value storedPrefix:ℝ)≤(P:ℝ) := by exact_mod_cast hPrefix
  have ht : (1-(e:ℝ))*(T:ℝ)≤(value storedTotal:ℝ) ∧ (value storedTotal:ℝ)≤(T:ℝ) := by exact_mod_cast hTotal
  have hs : (0:ℝ)<T := by exact_mod_cast hT
  have hpr : (0:ℝ)≤P := by exact_mod_cast hP
  have hptr : (P:ℝ)≤T := by exact_mod_cast hPT
  have her : (0:ℝ)≤e := by exact_mod_cast he
  have ho : (e:ℝ)<1 := by exact_mod_cast hOne
  have hc := comparison_branches w j s storedPrefix storedTotal (P:ℝ) (T:ℝ) (e:ℝ)
    hS hs hpr hptr her ho hp ht hLeft hRight
  constructor
  · intro h
    have hh : (((j:ℚ)/s-2*e/(1-e):ℚ):ℝ)≤((P/T:ℚ):ℝ) := by
      push_cast
      exact hc.1 h
    exact_mod_cast hh
  · intro h
    have hh : ((P/T:ℚ):ℝ)≤(((j:ℚ)/s+2*e/(1-e):ℚ):ℝ) := by
      push_cast
      exact hc.2 h
    exact_mod_cast hh

theorem choose_branches (lambda k j prefixExponent totalExponent : ℕ)
    (storedPrefix storedTotal : Number) (P T : ℚ)
    (hJ : j≤(GeneralPaperSourceParameters.prepare k).summarySize)
    (hT : 0<T) (hPT : P≤T)
    (hPE : prefixExponent≤budget lambda k) (hTE : totalExponent≤budget lambda k)
    (hPrefix : Bound (prepare lambda k).format.unit prefixExponent P storedPrefix)
    (hTotal : Bound (prepare lambda k).format.unit totalExponent T storedTotal) :
    ((choose lambda k j storedTotal storedPrefix).answer=true →
      (j:ℚ)/(GeneralPaperSourceParameters.prepare k).summarySize-delta k≤P/T) ∧
    ((choose lambda k j storedTotal storedPrefix).answer=false →
      P/T≤(j:ℚ)/(GeneralPaperSourceParameters.prepare k).summarySize+delta k) := by
  have hUnit : (prepare lambda k).format.unit=2^(prepare lambda k).format.fractionalBits :=
    GeneralPaperPowerPrecision.unit_power lambda k
  have hp := normal_mantissa_bits _ storedPrefix (hUnit ▸ hPrefix.1)
  have ht := normal_mantissa_bits _ storedTotal (hUnit ▸ hTotal.1)
  have hs := (GeneralPaperSourceParameters.data k).2.2.2.2.2
  have hLeft := GeneralPaperDyadicCompare.scale_bound _ (34+k) j storedTotal ht (by simpa only [hs] using hJ)
  have hRight := GeneralPaperDyadicCompare.scale_bound _ (34+k) (GeneralPaperSourceParameters.prepare k).summarySize storedPrefix hp (by rw [hs])
  have hPos : 0<(GeneralPaperSourceParameters.prepare k).summarySize := by rw [hs]; positivity
  exact comparison_rational (width lambda k) j _ storedPrefix storedTotal P T (error k)
    hPos hT hPrefix.2.1 hPT (error_bounds k).1.le (error_bounds k).2
    (selected_relative lambda k prefixExponent P storedPrefix hPE hPrefix)
    (selected_relative lambda k totalExponent T storedTotal hTE hTotal) hLeft hRight

theorem choose_work (lambda k j : ℕ) (storedTotal storedPrefix : Number) :
    (choose lambda k j storedTotal storedPrefix).work≤8*width lambda k+42 :=
  GeneralPaperDyadicCompare.scaled_work _ _ _ _ _

end Blotto.GeneralPaperQuantileComparison
