import Blotto.GeneralPaperIntegerMatrixSize

/-! Actual original dense rows and every leading minor inherit the sparse
row-mass bound. Prefix packing is an injection, with no dimension factor
introduced into the determinant envelope.
-/
namespace Blotto.GeneralPaperBasisRowSize
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperBasisStoredProducts
open GeneralPaperBasisFreshRHS GeneralPaperBasisInvariant GeneralPaperBasisPrefixSum
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem prefix_mass {j d : ℕ} (hj : j≤d) (f : Fin d → ℕ) :
    (∑ i : Fin j,f (embed hj i))≤∑ k : Fin d,f k := by
  have he : (∑ k ∈ Finset.univ.image (embed hj),f k)=∑ i : Fin j,f (embed hj i) := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact Fin.ext (congrArg (fun q : Fin d => q.val) hab)
  rw [←he]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem build_mass {T m K : ℕ} (hm : 0<m) (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (r : Index T m K scores h) (useSlope : Bool) :
    (∑ i : Fin (m*(K-1)),((GeneralPaperBasisDenseRow.build (constraints labels scores h r)).coefficients.read i).natAbs)+
      (if useSlope then (GeneralPaperBasisDenseRow.build (constraints labels scores h r)).slope
        else (GeneralPaperBasisDenseRow.build (constraints labels scores h r)).constant).natAbs≤m+1 := by
  have he : (∑ i : Fin (m*(K-1)),((GeneralPaperBasisDenseRow.build (constraints labels scores h r)).coefficients.read i).natAbs)=
      ∑ a : Variable m K,((constraints labels scores h r).coefficient a).natAbs := by
    symm
    apply Fintype.sum_equiv (GeneralPaperBasisCoordinates.equivalence m K)
    intro a
    change ((constraints labels scores h r).coefficient a).natAbs=
      ((GeneralPaperBasisDenseRow.build (constraints labels scores h r)).coefficients.read (GeneralPaperBasisCoordinates.index a)).natAbs
    rw [GeneralPaperBasisDenseRow.build_read]
  rw [he]
  exact GeneralPaperAffineConstraintMass.augmented_mass hm labels scores h r useSlope

theorem original_mass {T m K j : ℕ} (hm : 0<m) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1)))
    (hj : j≤m*(K-1)) (state : GeneralPaperBasisState.State j (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid hj state) (i : Fin j) (useSlope : Bool) :
    (∑ k,((state.rows.read i).coefficients.read k).natAbs)+
      (if useSlope then (state.rows.read i).slope else (state.rows.read i).constant).natAbs≤m+1 := by
  obtain ⟨r,hr⟩ := inv.original i
  rw [hr]
  exact build_mass hm dict.label (GeneralPaperStrictScore.score v S) h r useSlope

theorem build_coefficient {T m K : ℕ} (hm : 0<m) (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (r : Index T m K scores h) (a : Fin (m*(K-1))) :
    ((GeneralPaperBasisDenseRow.build (constraints labels scores h r)).coefficients.read a).natAbs≤m+1 := by
  have hr := build_mass hm labels scores h r false
  have hh : ((GeneralPaperBasisDenseRow.build (constraints labels scores h r)).coefficients.read a).natAbs≤
      ∑ k,((GeneralPaperBasisDenseRow.build (constraints labels scores h r)).coefficients.read k).natAbs :=
    Finset.single_le_sum (f:=fun k : Fin (m*(K-1)) => ((GeneralPaperBasisDenseRow.build (constraints labels scores h r)).coefficients.read k).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  omega

theorem minor_mass {T m K j : ℕ} (hm : 0<m) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1)))
    (hj : j≤m*(K-1)) (state : GeneralPaperBasisState.State j (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid hj state) (i : Fin j) (useSlope : Bool) :
    (∑ k,((minor state.rows hj) i k).natAbs)+
      (if useSlope then (state.rows.read i).slope else (state.rows.read i).constant).natAbs≤m+1 := by
  have hp := prefix_mass hj (fun k => ((state.rows.read i).coefficients.read k).natAbs)
  exact (Nat.add_le_add_right hp _).trans (original_mass hm dict v S h N betaN initialGrid hj state inv i useSlope)

theorem coefficient {T m K j : ℕ} (hm : 0<m) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1)))
    (hj : j≤m*(K-1)) (state : GeneralPaperBasisState.State j (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid hj state) (i : Fin j) (a : Fin (m*(K-1))) :
    ((state.rows.read i).coefficients.read a).natAbs≤m+1 := by
  have hr := original_mass hm dict v S h N betaN initialGrid hj state inv i false
  have hh : ((state.rows.read i).coefficients.read a).natAbs≤∑ k,((state.rows.read i).coefficients.read k).natAbs :=
    Finset.single_le_sum (f:=fun k : Fin (m*(K-1)) => ((state.rows.read i).coefficients.read k).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  omega

theorem rhs_entry {T m K j : ℕ} (hm : 0<m) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1)))
    (hj : j≤m*(K-1)) (state : GeneralPaperBasisState.State j (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid hj state) (i : Fin j) (useSlope : Bool) :
    (if useSlope then (state.rows.read i).slope else (state.rows.read i).constant).natAbs≤m+1 := by
  have hr := original_mass hm dict v S h N betaN initialGrid hj state inv i useSlope
  omega

end Blotto.GeneralPaperBasisRowSize
