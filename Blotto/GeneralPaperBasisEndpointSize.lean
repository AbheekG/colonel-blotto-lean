import Blotto.GeneralPaperEndpointRatioSize

/-! Exact denominator and unit-box bounds for the native original-basis
endpoint. The actual cached determinant is bounded from ORIGINAL rows.
No initializer scale occurs in the final numerator/denominator envelope.
-/
namespace Blotto.GeneralPaperBasisEndpointSize
open RationalOrderCell GeneralPaperBasisStoredProducts GeneralPaperBasisState GeneralPaperBasisInvariant
open GeneralPaperBasisOriginalDirection GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem determinant {T m K : ℕ} (hm : 0<m) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1)))
    (state : State (m*(K-1)) (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state) :
    state.determinant.natAbs≤(m+1)^(m*(K-1)) := by
  rw [←GeneralPaperBasisSelectedRows.determinant_identity dict v S h N betaN initialGrid state inv]
  exact GeneralPaperTransferDeterminantBounds.defining_determinant hm dict.label (GeneralPaperStrictScore.score v S) h _

theorem determinant_H {T m : ℕ} (k : ℕ) (hm : 0<m)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state) :
    state.determinant.natAbs≤(prepare m k).H := by
  apply (determinant hm dict v S h N betaN initialGrid state inv).trans
  rw [(data m k).2.2.2.1,(data m k).2.2.1]
  exact (Nat.pow_le_pow_left (by omega : m+1≤m+3) _).trans
    (Nat.pow_le_pow_right (by omega : 0<m+3) (by omega))

theorem entry_bounds {T m K : ℕ} (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (S h : ℕ) (state : State (m*(K-1)) (m*(K-1))) (hD : state.determinant≠0) (gamma : ℚ)
    (hEnd : GeneralPaperAffineConstraintRows.Feasible dict.label (GeneralPaperStrictScore.score v S) h (gamma:ℝ)
      (fun a => (reader (GeneralPaperBasisAffineEvaluate.atRational (GeneralPaperBasisAffineData.prepare state) gamma).1 a:ℝ)))
    (a : Variable m K) :
    (reader (GeneralPaperBasisAffineEvaluate.atRational (GeneralPaperBasisAffineData.prepare state) gamma).1 a).num.natAbs≤
        gamma.den*state.determinant.natAbs ∧
      (reader (GeneralPaperBasisAffineEvaluate.atRational (GeneralPaperBasisAffineData.prepare state) gamma).1 a).den≤
        gamma.den*state.determinant.natAbs := by
  have hBoxR := (GeneralPaperAffineConstraintSemantics.feasible_iff dict.label (GeneralPaperStrictScore.score v S) h _ _).mp hEnd
  have hBox : 0≤reader (GeneralPaperBasisAffineEvaluate.atRational (GeneralPaperBasisAffineData.prepare state) gamma).1 a ∧
      reader (GeneralPaperBasisAffineEvaluate.atRational (GeneralPaperBasisAffineData.prepare state) gamma).1 a≤1 := by
    exact_mod_cast hBoxR.1 a
  have hLat := GeneralPaperBasisAffineEvaluate.rational_lattice (GeneralPaperBasisAffineData.prepare state) hD gamma
    (GeneralPaperBasisCoordinates.index a)
  have hPos := Nat.mul_pos gamma.den_pos (Int.natAbs_pos.mpr hD)
  have ha : |reader (GeneralPaperBasisAffineEvaluate.atRational (GeneralPaperBasisAffineData.prepare state) gamma).1 a|≤(1:ℚ) := by
    rw [abs_of_nonneg hBox.1]
    exact hBox.2
  exact ⟨by simpa only [reader,one_mul] using rationalLattice_abs_numerator_le hPos hLat ha,
    rationalLattice_den_le hPos hLat⟩

theorem entry_height {T m : ℕ} (k : ℕ) (hm : 0<m)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state) (gamma : ℚ)
    (hGamma : gamma.den≤(prepare m k).qbar)
    (hEnd : GeneralPaperAffineConstraintRows.Feasible dict.label (GeneralPaperStrictScore.score v S) h (gamma:ℝ)
      (fun a => (reader (GeneralPaperBasisAffineEvaluate.atRational (GeneralPaperBasisAffineData.prepare state) gamma).1 a:ℝ)))
    (a : Variable m (prepare m k).K) :
    RationalHeight (reader (GeneralPaperBasisAffineEvaluate.atRational (GeneralPaperBasisAffineData.prepare state) gamma).1 a)
      (binaryWordWidth (prepare m k).qbar+binaryWordWidth (prepare m k).H) := by
  have hb := entry_bounds dict v S h state inv.nonzero gamma hEnd a
  have hd := determinant_H k hm dict v S h N betaN initialGrid state inv
  have he : gamma.den*state.determinant.natAbs≤(prepare m k).qbar*(prepare m k).H := Nat.mul_le_mul hGamma hd
  have hw := lt_pow_binaryWordWidth ((prepare m k).qbar*(prepare m k).H)
  have hHeight : RationalHeight (reader (GeneralPaperBasisAffineEvaluate.atRational (GeneralPaperBasisAffineData.prepare state) gamma).1 a)
      (binaryWordWidth ((prepare m k).qbar*(prepare m k).H)) := ⟨hb.1.trans_lt (he.trans_lt hw),hb.2.trans_lt (he.trans_lt hw)⟩
  exact hHeight.mono (binaryWordWidth_mul _ _)

end Blotto.GeneralPaperBasisEndpointSize
