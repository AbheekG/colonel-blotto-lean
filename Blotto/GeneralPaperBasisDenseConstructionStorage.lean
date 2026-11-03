import Blotto.GeneralPaperBasisScatterStorage

/-! Complete native original sparse-to-dense row construction. Sparse
input, mapped packed terms, coordinate arithmetic, zero fill/scatter, dense
coefficient/RHS/annotation return and all parent partial prices coexist. -/
namespace Blotto.GeneralPaperBasisDenseConstructionStorage
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperEncodedScalarStorage
open GeneralPaperStaticRowResidualStorage (termFoot termProfile rowFoot rowProfile)
open GeneralPaperBasisCoordinateStorage (packedTermFoot packedTermProfile)
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def annotation (d N : ℕ) : ℕ := 36*d+24*N+30
def price (model : RationalCostModel) (W d N : ℕ) : ℕ :=
  1024*(d+N+1)*(W+model.rat (1+binaryWordWidth (d+1))+model.rat (1+binaryWordWidth N))
def metadataCap (model : RationalCostModel) (W m K : ℕ) : ℕ :=
  m+K+m*(K-1)+(m+1)+1+3*price model W (m*(K-1)) (m+1)+annotation (m*(K-1)) (m+1)+(16*(m+1)+48)*W+(16*(m+1)+48)

def window {m K : ℕ} (model : RationalCostModel) (W copied : ℕ) (r : Row (Variable m K)) : ℕ :=
  let coordinates := GeneralPaperBasisCoordinateBits.run model.rat W r.terms
  let scattered := GeneralPaperBasisScatterBits.run model.rat W coordinates.1
  let result := GeneralPaperBasisDenseBits.run model.rat W r
  rowFoot W (termFoot W) r+GeneralPaperBasisCoordinateStorage.window model W r.terms+
    listFootprint W (packedTermFoot W) coordinates.1+GeneralPaperBasisScatterStorage.window model W copied coordinates.1+
    GeneralPaperEncodedBasisStorage.rowFootprint W result.1+
    fields W [m,K,m*(K-1),r.terms.length,coordinates.2,scattered.work,result.2,result.1.work,
      coordinates.2+scattered.work,(16*r.terms.length+48)*W,16*r.terms.length+48]+256*W

def profile (model : RationalCostModel) (W m K : ℕ) : ℕ :=
  rowProfile W m K+GeneralPaperBasisCoordinateStorage.profile model W m K (m+1)+
    GeneralPaperPricedPayloadStreamStorage.listProfile W (packedTermProfile W (m*(K-1))) (m+1)+
    GeneralPaperBasisScatterStorage.profile model W (m*(K-1)) (m+1)+
    GeneralPaperEncodedBasisStorage.rowProfile W (m*(K-1)) (m+1+1) (annotation (m*(K-1)) (m+1))+
    11*(natBits (metadataCap model W m K)+W)+288*W

theorem bounded {m K : ℕ} (model : RationalCostModel) (W copied : ℕ) (r : Row (Variable m K))
    (hn : r.terms.length≤m+1) (hu : ∀ t∈r.terms,t.2.natAbs≤1)
    (hc : r.constant.natAbs≤1) (hs : r.slope.natAbs≤1)
    (hW : 1≤W) (hIndex : binaryWordWidth (m*(K-1)+1)≤W) :
    window model W copied r≤profile model W m K := by
  let d := m*(K-1)
  let N := m+1
  let coordinates := GeneralPaperBasisCoordinateBits.run model.rat W r.terms
  let scattered := GeneralPaperBasisScatterBits.run model.rat W coordinates.1
  let result := GeneralPaperBasisDenseBits.run model.rat W r
  have hLen : coordinates.1.length=r.terms.length := by rw [GeneralPaperBasisCoordinateBits.data,List.length_map]
  have hUnit : ∀ t∈coordinates.1,t.2.natAbs≤1 := by
    rw [GeneralPaperBasisCoordinateBits.data]
    intro t ht; obtain ⟨u,hu',rfl⟩ := List.mem_map.mp ht; exact hu u hu'
  have hInput := GeneralPaperBlockerRowConstructionStorage.unit_row_bound W r hn hu hc hs
  have hCoordinates := GeneralPaperBasisCoordinateStorage.bounded model W (m+1) r.terms hn hu
  have hPacked := (list_bound W (packedTermProfile W d) (packedTermFoot W) coordinates.1
    (fun t ht => GeneralPaperBasisCoordinateStorage.packed_term_bound W t (hUnit t ht))).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ (hLen.le.trans hn)) _)
  have hScatter := GeneralPaperBasisScatterStorage.bounded model W (m+1) copied coordinates.1 (hLen.le.trans hn) hUnit hW hIndex
  have hZero : GeneralPaperBasisScatterStorage.Good 0 (GeneralPaperBasisScatterBits.zeroRun W d).1 := by
    intro i
    simp only [GeneralPaperBasisScatterBits.zeroRun,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn,Int.natAbs_zero,le_refl]
  have hCoefficient (i) : (result.1.coefficients.read i).natAbs≤m+1+1 := by
    have h := GeneralPaperBasisScatterStorage.loop_values model W 0 coordinates.1 (GeneralPaperBasisScatterBits.zeroRun W d).1 0 hUnit hZero i
    change (result.1.coefficients.read i).natAbs≤0+coordinates.1.length at h
    omega
  have hAnnotation : result.1.work≤annotation d N := by
    change 36*d+24*r.terms.length+30≤_
    unfold annotation
    dsimp only [N]
    omega
  have hOutput := GeneralPaperEncodedBasisStorage.row_bound W (m+1+1) (annotation d N) result.1 hCoefficient
    ⟨hc.trans (by omega),hs.trans (by omega)⟩ hAnnotation
  have hWork := (GeneralPaperBasisDenseBits.work model.rat model.monotone W hW hIndex r hu).trans
    (show 1024*(d+r.terms.length+1)*(W+model.rat (1+binaryWordWidth (d+1))+model.rat (1+binaryWordWidth r.terms.length))≤price model W d N by
      unfold price
      gcongr
      exact model.monotone (Nat.add_le_add_left (binaryWordWidth_mono hn) 1))
  change result.2≤price model W d N at hWork
  have hShape : result.2=coordinates.2+scattered.work+(16*r.terms.length+48)*W := rfl
  have hTermPrice := Nat.mul_le_mul_right W (Nat.add_le_add_right (Nat.mul_le_mul_left 16 hn) 48)
  have hf := fields_bound W (natBits (metadataCap model W m K))
    [m,K,d,r.terms.length,coordinates.2,scattered.work,result.2,result.1.work,
      coordinates.2+scattered.work,(16*r.terms.length+48)*W,16*r.terms.length+48] (by
      intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; dsimp only [d,N] at hWork hAnnotation hTermPrice ⊢; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤11*(natBits (metadataCap model W m K)+W)+32*W at hf
  unfold window profile GeneralPaperPricedPayloadStreamStorage.listProfile
  dsimp only
  dsimp only [d,N,coordinates,scattered,result] at hPacked hScatter hOutput hf
  omega

theorem original_bounded {T m K : ℕ} (model : RationalCostModel) (W copied : ℕ) (hm : 0<m)
    (labels : Fin T → Fin m → Fin K) (b : GeneralPaperRayBlockerRows.Descriptor T m K)
    (hW : 1≤W) (hIndex : binaryWordWidth (m*(K-1)+1)≤W) :
    window model W copied (GeneralPaperBlockerRowPrice.run W labels b).1≤profile model W m K := by
  apply bounded
  · rw [GeneralPaperBlockerRowPrice.data]
    exact GeneralPaperBlockerRowPrice.length hm labels b
  · cases b with
    | inl i =>
      rw [GeneralPaperBlockerRowPrice.data]
      exact GeneralPaperStaticRowPrice.unit_terms labels i
    | inr tuple =>
      intro t ht
      change t∈(GeneralPaperPricedListMap.run W (fun t => ((t.1,-t.2),8*W))
        (GeneralPaperBlockerRowPrice.tupleRun W tuple.read).1).1 at ht
      rw [GeneralPaperPricedListMap.data] at ht
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
      simpa only [Int.natAbs_neg] using GeneralPaperOriginalTupleConstructionStorage.terms_unit W tuple.read u hu
  · cases b with
    | inl i => rw [GeneralPaperBlockerRowPrice.data]; exact GeneralPaperStaticRowPrice.constant_unit labels i
    | inr tuple => change (0:ℤ).natAbs≤1; norm_num
  · cases b with
    | inl i =>
      rw [GeneralPaperBlockerRowPrice.data]
      exact (GeneralPaperAffineConstraintRows.rhs_unit labels (fun _ _ => 0) 0 (GeneralPaperStaticRayRows.embed i)).2
    | inr tuple => change (-1:ℤ).natAbs≤1; norm_num
  · exact hW
  · exact hIndex

end Blotto.GeneralPaperBasisDenseConstructionStorage
