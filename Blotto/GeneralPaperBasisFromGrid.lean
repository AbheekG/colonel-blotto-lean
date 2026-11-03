import Blotto.GeneralPaperBasisControllerSound

/-! Actual initializer controls and original rational N-grid data feed
the d-stage controller. The auxiliary numerator is derived in both
normalizations; no integer RHS or rationalization oracle is supplied.
-/
namespace Blotto.GeneralPaperBasisFromGrid
open RationalOrderCell GeneralPaperStrictScore GeneralPaperBasisStoredProducts
open GeneralPaperBasisCoordinates GeneralPaperBasisGridInputs GeneralPaperBasisInvariant
set_option autoImplicit false
set_option maxHeartbeats 4500000

def run {T m K : ℕ} (scoreDepth : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h H p q : ℕ) (reciprocal : Bool) (initial : Variable m K → ℚ) :
    Option (GeneralPaperBasisState.State (m*(K-1)) (m*(K-1))) :=
  let controls := GeneralPaperInitializerParameters.prepare m H p q reciprocal
  let initialGrid := grid controls.N initial
  GeneralPaperBasisController.run scoreDepth dict v S h controls.N (auxiliaryNumerator m H p q reciprocal) initialGrid

theorem run_valid {T m K : ℕ} (scoreDepth : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (hK : 0<K) (S h H p q : ℕ) (hCap : S<2^scoreDepth)
    (reciprocal : Bool) (hm : 0<m) (hH : 0<H) (hp : 0<p) (hq : 0<q)
    (initial : Variable m K → ℚ)
    (hGrid : ∀ a,OnRationalLattice (GeneralPaperInitializerParameters.prepare m H p q reciprocal).N (initial a))
    (hStart : GeneralPaperAffineConstraintRows.Feasible dict.label (score v S) h
      ((GeneralPaperInitializerParameters.prepare m H p q reciprocal).auxiliary:ℝ) (fun a => (initial a:ℝ))) :
    ∃ state,run scoreDepth dict v S h H p q reciprocal initial=some state ∧
      Invariant dict v S h (GeneralPaperInitializerParameters.prepare m H p q reciprocal).N
        (auxiliaryNumerator m H p q reciprocal)
        (grid (GeneralPaperInitializerParameters.prepare m H p q reciprocal).N initial) (Nat.le_refl _) state := by
  have hn := GeneralPaperInitializerParameters.N_positive m H p q reciprocal hm hH hp hq
  have hb : (auxiliaryNumerator m H p q reciprocal:ℝ)/
      ((GeneralPaperInitializerParameters.prepare m H p q reciprocal).N:ℝ)=
        ((GeneralPaperInitializerParameters.prepare m H p q reciprocal).auxiliary:ℝ) := by
    have hh := congrArg (fun r : ℚ => (r:ℝ)) (auxiliary_decode m H p q reciprocal hm hH hp hq)
    simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] using hh
  have hx (a : Variable m K) :
      ((grid (GeneralPaperInitializerParameters.prepare m H p q reciprocal).N initial).read (index a):ℝ)/
        ((GeneralPaperInitializerParameters.prepare m H p q reciprocal).N:ℝ)=(initial a:ℝ) := by
    have hh := congrArg (fun r : ℚ => (r:ℝ))
      (grid_decode (GeneralPaperInitializerParameters.prepare m H p q reciprocal).N hn initial hGrid a)
    simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] using hh
  have hPacked : GeneralPaperAffineConstraintRows.Feasible dict.label (score v S) h
      ((auxiliaryNumerator m H p q reciprocal:ℝ)/((GeneralPaperInitializerParameters.prepare m H p q reciprocal).N:ℝ))
      (fun a => ((grid (GeneralPaperInitializerParameters.prepare m H p q reciprocal).N initial).read (index a):ℝ)/
        ((GeneralPaperInitializerParameters.prepare m H p q reciprocal).N:ℝ)) := by
    simpa only [hb,hx] using hStart
  exact GeneralPaperBasisControllerSound.run_valid scoreDepth dict v hK S h
    (GeneralPaperInitializerParameters.prepare m H p q reciprocal).N hn hCap
    (auxiliaryNumerator m H p q reciprocal) (grid (GeneralPaperInitializerParameters.prepare m H p q reciprocal).N initial) hPacked

end Blotto.GeneralPaperBasisFromGrid
