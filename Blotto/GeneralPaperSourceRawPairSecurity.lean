import Blotto.GeneralPaperSourceUnchangedDictionary
import Blotto.GeneralPaperPreparedProxySource

/-! Paired security of the literal rational whole-row source tables in
the SAME native rational field values used by the endpoint/score phases.
All proxy/alphabet denominator premises come from the actual classifier.
-/
namespace Blotto.GeneralPaperSourceRawPairSecurity
open GeneralPaperProxyParameters GeneralPaperSourceInitializer GeneralPaperInitializerPreparedPoint
open GeneralPaperDictionary
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem values_determined {m : ℕ} (v w : Values m) (h : v.weight=w.weight) : v=w := by
  cases v
  cases w
  cases h
  rfl

theorem native_values {m : ℕ} (Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) :
    (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values=
      GeneralPaperCatalogueCanonicalGap.normalizedValues Qv hQv weights hp hs := by
  apply values_determined
  funext j
  exact GeneralPaperNativeRationalValues.real_weight Qv hQv weights hp hs j

theorem source_law {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    (law (GeneralPaperRowQuantizer.original (sourceRows k Qv weights b reciprocal))
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)).law=
      GeneralPaperCatalogueCanonicalGap.strategy false (alphabet m k) k Qv hm hQv weights hs
        (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
        (own_positive m k b hb reciprocal).le (prepare m k).qbar :=
  GeneralPaperCatalogueRationalTrajectory.law_eq (alphabet m k) k Qv (prepare m k).qbar hm hQv weights hs
    (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) (own_positive m k b hb reciprocal).le

theorem bound {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) :
    security (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values (opposingBudget m k b false:ℝ)
        (law (GeneralPaperRowQuantizer.original (sourceRows k Qv weights b false))
          (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)).law+
      security (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values (opposingBudget m k b true:ℝ)
        (law (GeneralPaperRowQuantizer.original (sourceRows k Qv weights b true))
          (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)).law≤
        1+3*((GeneralPaperSourceParameters.prepare k).z:ℝ)/32 := by
  cases m with
  | zero => omega
  | succ n =>
    rw [native_values,source_law k Qv hm hQv weights hs b hb false,source_law k Qv hm hQv weights hs b hb true]
    have hSource := GeneralPaperPreparedProxySource.source k Qv hQv weights hp hs b hb
    dsimp only at hSource
    simpa only [ownBudget,opposingBudget,GeneralPaperPreparedProxySource.ratio,Bool.false_eq_true,ite_false,ite_true,Rat.cast_one]
      using hSource.2.2

end Blotto.GeneralPaperSourceRawPairSecurity
