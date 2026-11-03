import Blotto.GeneralPaperRayAffineDPSize

/-! The actual native stage supplies common-lattice/magnitude bounds for
every literal ray anchor, including fixed zero labels. These same anchors
construct the executed parametric DP fields; no affine-cost oracle.
-/
namespace Blotto.GeneralPaperRayAnchorBound
open RationalOrderCell GeneralPaperRayRationalBound GeneralPaperBasisStoredProducts
open GeneralPaperBasisInvariant GeneralPaperBasisFreshRHS GeneralPaperBasisPrefixSum GeneralPaperProxyParameters
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem anchor {m K : ℕ} (D M : ℕ) (x : Variable m K → ℚ) (hx : ∀ a,Bounded D M (x a))
    (j : Fin m) (l : Fin K) : Bounded D M (GeneralPaperRayAnchorCosts.anchorQ x j l) := by
  unfold GeneralPaperRayAnchorCosts.anchorQ
  split
  · exact (Bounded.zero D).mono (Nat.zero_le M)
  · exact hx _

theorem fields {m K : ℕ} (D E X W : ℕ) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E W (w a)) :
    ∀ f∈GeneralPaperRayAffineScoreInput.fields matrix x w,GeneralPaperRayAffineDPSize.FieldBounded D E X W f := by
  intro f hf
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hf
  intro l
  simp only [FixedArrayTable.read_ofFn]
  exact ⟨anchor D X x hx j l,anchor E W w hw j l⟩

theorem point {T m j : ℕ} (k : ℕ) (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K)
    (v : RationalFieldSelector m) (S h N : ℕ) (hN : 0<N) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (hj : j≤m*((prepare m k).K-1)) (state : GeneralPaperBasisState.State j (m*((prepare m k).K-1)))
    (inv : Invariant dict v S h N betaN initialGrid hj state) (a : Variable m (prepare m k).K) :
    Bounded (N*state.determinant.natAbs) 1
      (GeneralPaperBasisOriginalDirection.reader
        (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point a) := by
  have hBoxR := ((GeneralPaperAffineConstraintSemantics.feasible_iff dict.label (GeneralPaperStrictScore.score v S) h _ _).mp inv.feasible).1 a
  dsimp only [GeneralPaperBasisFreshPointSound.values] at hBoxR
  have hBox : 0≤GeneralPaperBasisOriginalDirection.reader
      (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point a ∧
      GeneralPaperBasisOriginalDirection.reader
      (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point a≤1 := by exact_mod_cast hBoxR
  exact ⟨GeneralPaperBasisStageLattice.point N hN betaN state.determinant inv.nonzero state.adjugate state.rows initialGrid hj _,
    by rw [abs_of_nonneg hBox.1]; exact hBox.2⟩

theorem direction {T m j : ℕ} (k : ℕ) (hm : 0<m) (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K)
    (v : RationalFieldSelector m) (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (hj : j≤m*((prepare m k).K-1)) (state : GeneralPaperBasisState.State j (m*((prepare m k).K-1)))
    (inv : Invariant dict v S h N betaN initialGrid hj state)
    (next : Fin (m*((prepare m k).K-1))) (hNext : next.val=j) (a : Variable m (prepare m k).K) :
    Bounded state.determinant.natAbs (j*(prepare m k).H*(m+1)+1)
      (GeneralPaperBasisOriginalDirection.reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows next).velocity a) := by
  refine ⟨GeneralPaperBasisStageLattice.direction state.determinant inv.nonzero state.adjugate state.rows next hNext hj _,?_⟩
  let coord := GeneralPaperBasisCoordinates.index a
  change |(GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows next).velocity.read coord|≤_
  have hc := GeneralPaperBasisCacheSize.cache_H k hm dict v S h N betaN initialGrid hj state inv
  by_cases ha : coord.val<j
  · let i : Fin j := ⟨coord.val,ha⟩
    have he : embed hj i=coord := Fin.ext rfl
    have hCol (i : Fin j) : ((GeneralPaperBasisDirection.columnRun state.rows next).1.read i).natAbs≤m+1 := by
      rw [GeneralPaperBasisDirection.column_read]
      exact GeneralPaperBasisRowSize.coefficient hm dict v S h N betaN initialGrid hj state inv i next
    have hn := GeneralPaperStoredProductSize.mulVec state.adjugate (GeneralPaperBasisDirection.columnRun state.rows next).1
      (prepare m k).H (m+1) hc.2 hCol i
    rw [mulVec_data] at hn
    rw [←he,GeneralPaperBasisDirection.first_read _ _ _ _ hj i,GeneralPaperBasisRationalSolve.read]
    simp only [Nat.cast_one,one_mul,abs_neg]
    exact (abs_int_fraction _ _ inv.nonzero _ hn).trans (by exact_mod_cast Nat.le_succ (j*(prepare m k).H*(m+1)))
  · by_cases he : coord.val=j
    · have heq : coord=next := Fin.ext (he.trans hNext.symm)
      rw [heq,GeneralPaperBasisDirection.next_read _ _ _ _ hNext]
      rw [abs_one]
      exact_mod_cast (show 1≤j*(prepare m k).H*(m+1)+1 by omega)
    · rw [GeneralPaperBasisDirection.later_read _ _ _ _ coord (by omega),abs_zero]
      positivity

theorem budget (N : ℕ) (hN : 0<N) (D : ℕ) (betaN : ℤ) :
    Bounded (N*D) betaN.natAbs ((betaN:ℚ)/(N:ℚ)) := by
  have hn : (N:ℤ)≠0 := by exact_mod_cast hN.ne'
  have hl := FinitePolytopeRationalWitness.denominator_divInt (numerator:=betaN) (denominator:=(N:ℤ)) hn
  have hLattice : OnRationalLattice N ((betaN:ℚ)/(N:ℚ)) := by
    simpa only [OnRationalLattice,Int.cast_natCast,Int.natAbs_natCast] using hl
  exact ⟨hLattice.enlarge (Nat.dvd_mul_right N D),by
    simpa only [Int.cast_natCast] using abs_int_fraction betaN (N:ℤ) hn betaN.natAbs le_rfl⟩

end Blotto.GeneralPaperRayAnchorBound
