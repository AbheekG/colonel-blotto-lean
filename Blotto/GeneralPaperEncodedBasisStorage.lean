import Blotto.GeneralPaperBasisControllerBits
import Blotto.GeneralPaperEncodedRationalRows
import Blotto.GeneralPaperReferenceScaling

/-! Encoded ownership of an actual retained original-row basis. The observer
includes dense coefficients, both row RHS values, native row work fields,
the determinant, the adjugate and all array references/headers. Original-row
provenance supplies every bound, including the row work fields. This is an
erased observer, not a runtime traversal or a whole-controller lifetime claim. -/
namespace Blotto.GeneralPaperEncodedBasisStorage
open GeneralPaperBasisStoredProducts GeneralPaperBasisState GeneralPaperBasisInvariant
open GeneralPaperEncodedScalarStorage GeneralPaperProxyParameters
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

def integerBits (z : ℤ) : ℕ := 1+binaryWordWidth z.natAbs

def arrayFootprint {α : Type*} {n : ℕ} (W : ℕ) (encode : α → ℕ) (a : FixedArrayTable n α) : ℕ :=
  64*W+∑ i : Fin n, (W+encode (a.read i))

def arrayProfile (W n P : ℕ) : ℕ := n*(W+P)+64*W

theorem array_bound {α : Type*} {n : ℕ} (W P : ℕ) (encode : α → ℕ) (a : FixedArrayTable n α)
    (h : ∀ i,encode (a.read i)≤P) : arrayFootprint W encode a≤arrayProfile W n P := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => Nat.add_le_add_left (h i) W)
  simpa only [arrayFootprint,arrayProfile,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.add_comm] using Nat.add_le_add_left hs (64*W)

def rowFootprint {d : ℕ} (W : ℕ) (r : GeneralPaperBasisDenseRow.Dense d) : ℕ :=
  arrayFootprint W integerBits r.coefficients+integerBits r.constant+integerBits r.slope+natBits r.work+32*W

def rowProfile (W d M F : ℕ) : ℕ :=
  arrayProfile W d (1+binaryWordWidth M)+2*(1+binaryWordWidth M)+natBits F+32*W

theorem row_bound {d : ℕ} (W M F : ℕ) (r : GeneralPaperBasisDenseRow.Dense d)
    (hc : ∀ i,(r.coefficients.read i).natAbs≤M) (hr : r.constant.natAbs≤M ∧ r.slope.natAbs≤M)
    (hf : r.work≤F) : rowFootprint W r≤rowProfile W d M F := by
  have hA := array_bound W (1+binaryWordWidth M) integerBits r.coefficients
    (fun i => Nat.add_le_add_left (binaryWordWidth_mono (hc i)) 1)
  have hC : integerBits r.constant≤1+binaryWordWidth M := Nat.add_le_add_left (binaryWordWidth_mono hr.1) 1
  have hS : integerBits r.slope≤1+binaryWordWidth M := Nat.add_le_add_left (binaryWordWidth_mono hr.2) 1
  have hF : natBits r.work≤natBits F := Nat.add_le_add_left (binaryWordWidth_mono hf) 1
  unfold rowFootprint rowProfile
  omega

def footprint {j d : ℕ} (W : ℕ) (state : State j d) : ℕ :=
  arrayFootprint W (rowFootprint W) state.rows+integerBits state.determinant+
    arrayFootprint W (arrayFootprint W integerBits) state.adjugate+32*W

def profile (W j d M H F : ℕ) : ℕ :=
  arrayProfile W j (rowProfile W d M F)+(1+binaryWordWidth H)+
    arrayProfile W j (arrayProfile W j (1+binaryWordWidth H))+32*W

theorem state_bound {j d : ℕ} (W M H F : ℕ) (state : State j d)
    (hc : ∀ i a,((state.rows.read i).coefficients.read a).natAbs≤M)
    (hr : ∀ i,(state.rows.read i).constant.natAbs≤M ∧ (state.rows.read i).slope.natAbs≤M)
    (hf : ∀ i,(state.rows.read i).work≤F) (hD : state.determinant.natAbs≤H)
    (hA : ∀ i a,((state.adjugate.read i).read a).natAbs≤H) :
    footprint W state≤profile W j d M H F := by
  have hR := array_bound W (rowProfile W d M F) (rowFootprint W) state.rows
    (fun i => row_bound W M F (state.rows.read i) (hc i) (hr i) (hf i))
  have hAdj := array_bound W (arrayProfile W j (1+binaryWordWidth H)) (arrayFootprint W integerBits) state.adjugate
    (fun i => array_bound W (1+binaryWordWidth H) integerBits (state.adjugate.read i)
      (fun a => Nat.add_le_add_left (binaryWordWidth_mono (hA i a)) 1))
  have hDet : integerBits state.determinant≤1+binaryWordWidth H := Nat.add_le_add_left (binaryWordWidth_mono hD) 1
  unfold footprint profile
  omega

def rowWork (d m : ℕ) : ℕ := 64*(d+1)+24*(m+1)+14

theorem original_work {T m K j : ℕ} (hm : 0<m) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1)))
    (hj : j≤m*(K-1)) (state : State j (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid hj state) (i : Fin j) :
    (state.rows.read i).work≤rowWork (m*(K-1)) m := by
  obtain ⟨r,hr⟩ := inv.original i
  rw [hr]
  have hw := GeneralPaperBasisDenseRow.build_work (GeneralPaperAffineConstraintRows.constraints dict.label (GeneralPaperStrictScore.score v S) h r)
  have ht := GeneralPaperAffineConstraintMass.augmented_terms hm dict.label (GeneralPaperStrictScore.score v S) h r false
  unfold rowWork
  omega

def paperProfile (W m k : ℕ) : ℕ :=
  let d := m*((prepare m k).K-1)
  profile W d d (m+1) (prepare m k).H (rowWork d m)

theorem invariant_bound {T m j : ℕ} (W k : ℕ) (hm : 0<m)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (hj : j≤m*((prepare m k).K-1)) (state : State j (m*((prepare m k).K-1)))
    (inv : Invariant dict v S h N betaN initialGrid hj state) :
    footprint W state≤paperProfile W m k := by
  have hCache := GeneralPaperBasisCacheSize.cache_H k hm dict v S h N betaN initialGrid hj state inv
  have hb := state_bound W (m+1) (prepare m k).H (rowWork (m*((prepare m k).K-1)) m) state
    (GeneralPaperBasisRowSize.coefficient hm dict v S h N betaN initialGrid hj state inv)
    (fun i => ⟨GeneralPaperBasisRowSize.rhs_entry hm dict v S h N betaN initialGrid hj state inv i false,
      GeneralPaperBasisRowSize.rhs_entry hm dict v S h N betaN initialGrid hj state inv i true⟩)
    (original_work hm dict v S h N betaN initialGrid hj state inv) hCache.1 hCache.2
  apply hb.trans
  dsimp only [paperProfile]
  unfold profile arrayProfile
  gcongr

theorem actual_stage {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (hm : 0<m) (scoreDepth : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K) (v : RationalFieldSelector m)
    (S h N : ℕ) (hN : 0<N) (hCap : S<2^scoreDepth) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (hStart : GeneralPaperAffineConstraintRows.Feasible dict.label (GeneralPaperStrictScore.score v S) h ((betaN:ℝ)/(N:ℝ))
      (fun a => (initialGrid.read (GeneralPaperBasisCoordinates.index a):ℝ)/(N:ℝ)))
    (j : ℕ) (hj : j≤m*((prepare m k).K-1)) (state : State j (m*((prepare m k).K-1)))
    (hr : (GeneralPaperBasisControllerBits.stages model W dict.label (GeneralPaperScoreMatrixWork.matrixRun scoreDepth dict v S).1
      S h N betaN initialGrid j hj).1=some state) : footprint W state≤paperProfile W m k := by
  obtain ⟨actual,ha,inv⟩ := GeneralPaperBasisControllerSound.stages_valid scoreDepth dict v
    (GeneralPaperScoreScaleParameters.labels_positive m k) S h N hN hCap betaN initialGrid hStart j hj
  rw [GeneralPaperBasisControllerBits.stages_data,ha] at hr
  cases Option.some.inj hr
  exact invariant_bound W k hm dict v S h N betaN initialGrid hj _ inv

@[fun_prop]
theorem profile_scale (j d M H F : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => profile W j d M H F) := by
  unfold profile rowProfile arrayProfile
  fun_prop

@[fun_prop]
theorem paper_profile_scale (m k : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => paperProfile W m k) :=
  profile_scale _ _ _ _ _

end Blotto.GeneralPaperEncodedBasisStorage
