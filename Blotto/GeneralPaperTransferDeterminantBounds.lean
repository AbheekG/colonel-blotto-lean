import Blotto.GeneralPaperAffineConstraintSemantics

/-! Uniform strict determinant bounds for the ACTUAL affine transfer
matrices, before any dictionary/score data are generated. Augmented rows
have mass at most m+1, yielding strict (m+2)^(d+1) and H envelopes.
Identification with residual numerator/slope still needs its algebraic join.
-/
namespace Blotto.GeneralPaperTransferDeterminantBounds
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperTransferMatrices
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem bordered_strict {T m K : ℕ} (hm : 0<m) (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (selected : Variable m K → Index T m K scores h)
    (extra : Index T m K scores h) (useSlope : Bool) :
    (bordered labels scores h selected extra useSlope).det.natAbs<(m+2)^(m*(K-1)+1) :=
  (bordered_determinant hm labels scores h selected extra useSlope).trans_lt
    (Nat.pow_lt_pow_left (by omega) (by omega))

theorem root_envelope (m K : ℕ) : (m+2)^(m*(K-1)+1)<(m+3)^(m*(K-1)+2) := by
  have hb : (m+2)^(m*(K-1)+1)<(m+3)^(m*(K-1)+1) := Nat.pow_lt_pow_left (by omega) (by omega)
  have he := Nat.pow_le_pow_right (by omega : 0<m+3) (show m*(K-1)+1≤m*(K-1)+2 by omega)
  exact hb.trans_le he

theorem bordered_H {T m : ℕ} (k : ℕ) (hm : 0<m)
    (labels : Fin T → Fin m → Fin (GeneralPaperProxyParameters.prepare m k).K)
    (scores : Fin m → Fin (GeneralPaperProxyParameters.prepare m k).K → ℕ) (h : ℕ)
    (selected : Variable m (GeneralPaperProxyParameters.prepare m k).K →
      Index T m (GeneralPaperProxyParameters.prepare m k).K scores h)
    (extra : Index T m (GeneralPaperProxyParameters.prepare m k).K scores h) (useSlope : Bool) :
    (bordered labels scores h selected extra useSlope).det.natAbs<(GeneralPaperProxyParameters.prepare m k).H := by
  have hb := (bordered_strict hm labels scores h selected extra useSlope).trans (root_envelope m _)
  rw [(GeneralPaperProxyParameters.data m k).2.2.2.1,(GeneralPaperProxyParameters.data m k).2.2.1]
  exact hb

theorem defining_determinant {T m K : ℕ} (hm : 0<m) (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (selected : Variable m K → Index T m K scores h) :
    (matrix labels scores h selected).det.natAbs≤(m+1)^(m*(K-1)) := by
  apply (FinitePolytopeRationalWitness.det_natAbs_le_rowMass _).trans
  have hRow (i : Variable m K) : (∑ j,((matrix labels scores h selected) i j).natAbs)≤m+1 := by
    have ha := GeneralPaperAffineConstraintMass.augmented_mass hm labels scores h (selected i) false
    change (∑ j,((constraints labels scores h (selected i)).coefficient j).natAbs)≤_
    omega
  have hp := Finset.prod_le_prod (s:=Finset.univ) (fun i _ => hRow i)
  simpa only [Finset.prod_const,Finset.card_univ,variable_card] using hp

end Blotto.GeneralPaperTransferDeterminantBounds
