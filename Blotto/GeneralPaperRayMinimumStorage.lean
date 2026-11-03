import Blotto.GeneralPaperHighMinimumStorage
import Blotto.GeneralPaperEncodedScoreMatrixStorage
import Blotto.GeneralPaperRayMinimumBits

/-! Post-DP storage of the actual fixed-probe ray minimum. The generated
cost fields remain owned through the high-score scan; their copied scores
and rational heights follow from the stored input matrix and actual ray
operands. Native parent/wrapper counters are encoded, not charged as time.
Field construction and active DP-layer windows are separate phases. -/
namespace Blotto.GeneralPaperRayMinimumStorage
open RationalOrderCell GeneralPaperExactScoreDP GeneralPaperEncodedScalarStorage
open GeneralPaperRayRationalBound GeneralPaperEncodedScoreMatrixStorage
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def height (D M : ℕ) : ℕ := binaryWordWidth (M+1)+binaryWordWidth D

def price (model : RationalCostModel) (W m K S D M : ℕ) : ℕ :=
  GeneralPaperRayMinimumBits.profile m K S W (model.rat (GeneralPaperCommonLatticeDPBits.width D M m))

def metadataCap (model : RationalCostModel) (W m K S D M : ℕ) : ℕ :=
  m+K+S+1+price model W m K S D M

def window {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (t : ℚ) (S h : ℕ) : ℕ :=
  let generated := GeneralPaperRayFieldsBits.matrixRun model W matrix x w t
  let inputs := GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t
  let minimum := GeneralPaperCommonLatticeMinimumBits.run model W S h inputs.1
  let result := GeneralPaperRayMinimumBits.run model W matrix x w t S h
  matrixFootprint W generated.1+listFootprint W (fun _ : Field K => 0) inputs.1+
    GeneralPaperHighMinimumStorage.window model W S h inputs.1+
    fields W [S,h,inputs.2,minimum.2,result.2,inputs.2+minimum.2]+256*W

def profile (model : RationalCostModel) (W m K S D M : ℕ) : ℕ :=
  matrixProfile W m K S (height D M)+m*(2*W)+32*W+
    GeneralPaperHighMinimumStorage.profile model W K S (height D M) m+
    6*(natBits (metadataCap model W m K S D M)+W)+32*W+256*W

theorem bounded {m K : ℕ} (model : RationalCostModel) (W D E X V S h : ℕ) (hD : 0<D) (hED : E∣D)
    (matrix : FixedArrayTable m (Field K)) (hs : ∀ j l,((matrix.read j).read l).1≤S)
    (x w : Variable m K → ℚ) (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a))
    (t : ℚ) (ht : 0≤t ∧ t≤1) (hh : h≤S)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth (S+2)≤W) :
    window model W matrix x w t S h≤profile model W m K S (D*t.den) (X+V+1) := by
  let generated := GeneralPaperRayFieldsBits.matrixRun model W matrix x w t
  let inputs := GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t
  let minimum := GeneralPaperCommonLatticeMinimumBits.run model W S h inputs.1
  let result := GeneralPaperRayMinimumBits.run model W matrix x w t S h
  have hLattice := GeneralPaperRayFieldsBits.fields_bounded model W D E X V hED matrix x w hx hw t ht
  have hPositive := Nat.mul_pos hD t.den_pos
  have hHeight : CostHeight inputs.1 (height (D*t.den) (X+V+1)) := by
    intro f hf l
    exact (hLattice f hf l).height hPositive
  have hLen : inputs.1.length=m := by
    dsimp only [inputs]
    rw [GeneralPaperRayFieldsBits.fields_data]
    simp only [GeneralPaperExactScoreDP.fields,List.length_ofFn]
  have hScan := GeneralPaperHighMinimumStorage.bounded model W S h (height (D*t.den) (X+V+1)) m
    inputs.1 hHeight hLen.le hh hW hIndex
  have hMatrix : matrixFootprint W generated.1≤matrixProfile W m K S (height (D*t.den) (X+V+1)) := by
    dsimp only [generated]
    rw [GeneralPaperRayFieldsBits.matrix_data]
    apply matrix_bound
    · intro j l
      simpa only [FixedArrayTable.read_ofFn,GeneralPaperRayQueryWork.scores] using hs j l
    · intro j l
      simp only [FixedArrayTable.read_ofFn]
      exact (GeneralPaperRayCostBits.operands D E X V hED x w hx hw t ht j l).2.2.2.2.height hPositive
  have hList : listFootprint W (fun _ : Field K => 0) inputs.1=m*(2*W)+32*W :=
    borrowed_fields W generated.1
  have hWork := GeneralPaperRayMinimumBits.work model W D E X V hD hED matrix x w hx hw t ht S h hW hK hM hIndex
  change result.2≤price model W m K S (D*t.den) (X+V+1) at hWork
  have hTimeShape : result.2=inputs.2+minimum.2+8*W := rfl
  have hf := fields_bound W (natBits (metadataCap model W m K S (D*t.den) (X+V+1)))
    [S,h,inputs.2,minimum.2,result.2,inputs.2+minimum.2] (by
      intro n hn
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤
    6*(natBits (metadataCap model W m K S (D*t.den) (X+V+1))+W)+32*W at hf
  change matrixFootprint W generated.1+listFootprint W (fun _ : Field K => 0) inputs.1+
    GeneralPaperHighMinimumStorage.window model W S h inputs.1+
    GeneralPaperEncodedScalarStorage.fields W [S,h,inputs.2,minimum.2,result.2,inputs.2+minimum.2]+256*W≤_
  unfold profile
  omega

theorem native_matrix {T m K : ℕ} (model : RationalCostModel) (W depth S D E X V : ℕ)
    (hD : 0<D) (hED : E∣D) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (v : RationalFieldSelector m) (hK : 0<K) (hCap : S<2^depth)
    (x w : Variable m K → ℚ) (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a))
    (t : ℚ) (ht : 0≤t ∧ t≤1) (h : ℕ) (hh : h≤S)
    (hW : 1≤W) (hLabel : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth (S+2)≤W) :
    window model W (GeneralPaperPhysicalScoreMatrix.run true model W depth columns v S).1 x w t S h≤
      profile model W m K S (D*t.den) (X+V+1) := by
  apply bounded model W D E X V S h hD hED _ _ x w hx hw t ht hh hW hLabel hM hIndex
  intro j l
  rw [GeneralPaperPhysicalScoreMatrix.data true model W depth columns v S hK hCap]
  simpa only [FixedArrayTable.read_ofFn] using score_bound v S hK j l

end Blotto.GeneralPaperRayMinimumStorage
