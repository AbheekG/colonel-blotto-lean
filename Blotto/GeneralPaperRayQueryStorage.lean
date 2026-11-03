import Blotto.GeneralPaperRayFieldConstructionStorage
import Blotto.GeneralPaperScoreInitialStorage

/-! Phase coverage for the actual fixed-probe native minimum. Generated
ray fields stay owned through initialization, each active DP layer and the
final high-score scan. The parent retains encoded return/work metadata in
every phase. Only one active DP layer is charged, not all past tables.
The enclosing matrix/point/direction owners and predicate wrapper remain
separate. Phase cursors and storage profiles are erased observers. -/
namespace Blotto.GeneralPaperRayQueryStorage
open RationalOrderCell GeneralPaperExactScoreDP GeneralPaperRayRationalBound
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedScoreMatrixStorage
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

def resident {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (t : ℚ) : ℕ :=
  matrixFootprint W (GeneralPaperRayFieldsBits.matrixRun model W matrix x w t).1+
    listFootprint W (fun _ : Field K => 0) (GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t).1+256*W

def residentProfile (W m K S D M : ℕ) : ℕ :=
  matrixProfile W m K S (GeneralPaperRayMinimumStorage.height D M)+m*(2*W)+32*W+256*W

theorem fields_height {m K : ℕ} (model : RationalCostModel) (W D E X V : ℕ) (hD : 0<D) (hED : E∣D)
    (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a)) (t : ℚ) (ht : 0≤t ∧ t≤1) :
    CostHeight (GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t).1
      (GeneralPaperRayMinimumStorage.height (D*t.den) (X+V+1)) :=
  fun f hf l => (GeneralPaperRayFieldsBits.fields_bounded model W D E X V hED matrix x w hx hw t ht f hf l).height
    (Nat.mul_pos hD t.den_pos)

theorem fields_length {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (t : ℚ) : (GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t).1.length=m := by
  rw [GeneralPaperRayFieldsBits.fields_data]
  simp only [GeneralPaperExactScoreDP.fields,List.length_ofFn]

theorem resident_bound {m K : ℕ} (model : RationalCostModel) (W S D E X V : ℕ) (hD : 0<D) (hED : E∣D)
    (matrix : FixedArrayTable m (Field K)) (hs : ∀ j l,((matrix.read j).read l).1≤S)
    (x w : Variable m K → ℚ) (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a))
    (t : ℚ) (ht : 0≤t ∧ t≤1) :
    resident model W matrix x w t≤residentProfile W m K S (D*t.den) (X+V+1) := by
  have hm : matrixFootprint W (GeneralPaperRayFieldsBits.matrixRun model W matrix x w t).1≤
      matrixProfile W m K S (GeneralPaperRayMinimumStorage.height (D*t.den) (X+V+1)) := by
    rw [GeneralPaperRayFieldsBits.matrix_data]
    apply matrix_bound
    · intro j l
      simpa only [FixedArrayTable.read_ofFn,GeneralPaperRayQueryWork.scores] using hs j l
    · intro j l
      simp only [FixedArrayTable.read_ofFn]
      exact (GeneralPaperRayCostBits.operands D E X V hED x w hx hw t ht j l).2.2.2.2.height (Nat.mul_pos hD t.den_pos)
  have hl : listFootprint W (fun _ : Field K => 0) (GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t).1=
      m*(2*W)+32*W := borrowed_fields W (GeneralPaperRayFieldsBits.matrixRun model W matrix x w t).1
  unfold resident residentProfile
  omega

def frame {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (t : ℚ) (S h : ℕ) : ℕ :=
  let generated := GeneralPaperRayFieldsBits.matrixRun model W matrix x w t
  let inputs := GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t
  let minimum := GeneralPaperCommonLatticeMinimumBits.run model W S h inputs.1
  let result := GeneralPaperRayMinimumBits.run model W matrix x w t S h
  fields W [S,h,generated.2,inputs.2,minimum.2,result.2,inputs.2+minimum.2,(8*m+4)*W]+rationalWordWidth t+256*W

def frameProfile (model : RationalCostModel) (W m K S D M : ℕ) : ℕ :=
  8*(natBits (GeneralPaperRayMinimumStorage.metadataCap model W m K S D M)+W)+32*W+
    (1+2*GeneralPaperRayMinimumStorage.height D M)+256*W

theorem frame_bound {m K : ℕ} (model : RationalCostModel) (W S h D E X V : ℕ) (hD : 0<D) (hED : E∣D)
    (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a))
    (t : ℚ) (ht : 0≤t ∧ t≤1) (hh : h≤S)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    frame model W matrix x w t S h≤frameProfile model W m K S (D*t.den) (X+V+1) := by
  let generated := GeneralPaperRayFieldsBits.matrixRun model W matrix x w t
  let inputs := GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t
  let minimum := GeneralPaperCommonLatticeMinimumBits.run model W S h inputs.1
  let result := GeneralPaperRayMinimumBits.run model W matrix x w t S h
  have hWork := GeneralPaperRayMinimumBits.work model W D E X V hD hED matrix x w hx hw t ht S h hW hK hM hIndex
  change result.2≤GeneralPaperRayMinimumStorage.price model W m K S (D*t.den) (X+V+1) at hWork
  have hResult : result.2=inputs.2+minimum.2+8*W := rfl
  have hInputs : inputs.2=generated.2+(8*m+4)*W := rfl
  have hf := fields_bound W (natBits (GeneralPaperRayMinimumStorage.metadataCap model W m K S (D*t.den) (X+V+1)))
    [S,h,generated.2,inputs.2,minimum.2,result.2,inputs.2+minimum.2,(8*m+4)*W] (by
      intro n hn
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold GeneralPaperRayMinimumStorage.metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤
    8*(natBits (GeneralPaperRayMinimumStorage.metadataCap model W m K S (D*t.den) (X+V+1))+W)+32*W at hf
  have hT : Bounded t.den 1 t := ⟨dvd_refl _,by rw [abs_of_nonneg ht.1]; exact ht.2⟩
  have hT' := (hT.enlarge (show t.den∣D*t.den from ⟨D,by ring⟩)).mono (show 1≤X+V+1 by omega)
  have hwT := rationalWordWidth_of_height (hT'.height (Nat.mul_pos hD t.den_pos))
  change rationalWordWidth t≤1+2*GeneralPaperRayMinimumStorage.height (D*t.den) (X+V+1) at hwT
  change GeneralPaperEncodedScalarStorage.fields W
    [S,h,generated.2,inputs.2,minimum.2,result.2,inputs.2+minimum.2,(8*m+4)*W]+rationalWordWidth t+256*W≤_
  unfold frameProfile
  omega

inductive Phase {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (t : ℚ) (S : ℕ) where
  | construct (outer : ℕ) (ho : outer≤m) (j : Fin m) (inner : ℕ) (hi : inner≤K) (l : Fin K)
  | initial (count : ℕ) (hc : count≤S+1)
  | layer (field : Field K) (rest : List (Field K))
      (hSub : (field::rest).Sublist (GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t).1)
      (count : ℕ) (hc : count≤S+1) (s : Fin (S+1)) (xs : List (Fin K)) (hXs : xs.length≤K)
  | minimum

def window {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (t : ℚ) (S h : ℕ) (phase : Phase model W matrix x w t S) : ℕ :=
  frame model W matrix x w t S h+match phase with
  | .construct outer ho j inner hi l => GeneralPaperRayFieldConstructionStorage.window model W matrix x w t outer ho j inner hi l
  | .initial count hc => resident model W matrix x w t+
      GeneralPaperScoreLifetimeStorage.callerFrames model W S (GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t).1+
      GeneralPaperScoreInitialStorage.window model W K S count hc
  | .layer field rest _ count hc s xs _ => resident model W matrix x w t+
      (GeneralPaperScoreLifetimeStorage.callerFrames model W S (GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t).1+
        GeneralPaperScoreConstructionStorage.stepWindow model W field rest count hc s xs)
  | .minimum => GeneralPaperRayMinimumStorage.window model W matrix x w t S h

def profile (model : RationalCostModel) (W m K S D M : ℕ) : ℕ :=
  let A := GeneralPaperRayMinimumStorage.height D M
  frameProfile model W m K S D M+GeneralPaperRayFieldConstructionStorage.profile model W m K S D M+
    residentProfile W m K S D M+GeneralPaperScoreLifetimeStorage.callerProfile model W K S A m+
    GeneralPaperScoreInitialStorage.profile W K S+GeneralPaperScoreLifetimeStorage.layerProfile model W K S A m+
    GeneralPaperRayMinimumStorage.profile model W m K S D M

theorem all_phases {m K : ℕ} (model : RationalCostModel) (W S h D E X V : ℕ) (hD : 0<D) (hED : E∣D)
    (matrix : FixedArrayTable m (Field K)) (hs : ∀ j l,((matrix.read j).read l).1≤S)
    (x w : Variable m K → ℚ) (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a))
    (t : ℚ) (ht : 0≤t ∧ t≤1) (hh : h≤S)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W) (hIndex : binaryWordWidth (S+2)≤W)
    (phase : Phase model W matrix x w t S) :
    window model W matrix x w t S h phase≤profile model W m K S (D*t.den) (X+V+1) := by
  have hf := frame_bound model W S h D E X V hD hED matrix x w hx hw t ht hh hW hK hM hIndex
  have hr := resident_bound model W S D E X V hD hED matrix hs x w hx hw t ht
  have hHeight := fields_height model W D E X V hD hED matrix x w hx hw t ht
  have hLen := (fields_length model W matrix x w t).le
  cases phase with
  | construct outer ho j inner hi l =>
    have hc := GeneralPaperRayFieldConstructionStorage.bounded model W S D E X V hD hED matrix hs x w hx hw t ht
      hW hK hM outer ho j inner hi l
    change frame model W matrix x w t S h+GeneralPaperRayFieldConstructionStorage.window model W matrix x w t outer ho j inner hi l≤_
    dsimp only [profile]
    omega
  | initial count hc =>
    have hCaller := GeneralPaperScoreLifetimeStorage.caller_profile model W S _ m _ hHeight hLen hW hIndex
    have hi := GeneralPaperScoreInitialStorage.bounded model W K S hW hIndex count hc
    change frame model W matrix x w t S h+(resident model W matrix x w t+
      GeneralPaperScoreLifetimeStorage.callerFrames model W S (GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t).1+
      GeneralPaperScoreInitialStorage.window model W K S count hc)≤_
    dsimp only [profile]
    omega
  | layer field rest hSub count hc s xs hXs =>
    have hl := GeneralPaperScoreLifetimeStorage.actual_layer model W _ m _ hHeight hLen hW hIndex field rest hSub count hc s xs hXs
    change frame model W matrix x w t S h+(resident model W matrix x w t+
      (GeneralPaperScoreLifetimeStorage.callerFrames model W S (GeneralPaperRayFieldsBits.fieldsRun model W matrix x w t).1+
        GeneralPaperScoreConstructionStorage.stepWindow model W field rest count hc s xs))≤_
    dsimp only [profile]
    omega
  | minimum =>
    have hm := GeneralPaperRayMinimumStorage.bounded model W D E X V S h hD hED matrix hs x w hx hw t ht hh hW hK hM hIndex
    change frame model W matrix x w t S h+GeneralPaperRayMinimumStorage.window model W matrix x w t S h≤_
    dsimp only [profile]
    omega

theorem native_matrix {T m K : ℕ} (model : RationalCostModel) (W depth S h D E X V : ℕ)
    (hD : 0<D) (hED : E∣D) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (v : RationalFieldSelector m) (hK : 0<K) (hCap : S<2^depth)
    (x w : Variable m K → ℚ) (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a))
    (t : ℚ) (ht : 0≤t ∧ t≤1) (hh : h≤S)
    (hW : 1≤W) (hLabel : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W) (hIndex : binaryWordWidth (S+2)≤W)
    (phase : Phase model W (GeneralPaperPhysicalScoreMatrix.run true model W depth columns v S).1 x w t S) :
    window model W (GeneralPaperPhysicalScoreMatrix.run true model W depth columns v S).1 x w t S h phase≤
      profile model W m K S (D*t.den) (X+V+1) := by
  apply all_phases model W S h D E X V hD hED _ _ x w hx hw t ht hh hW hLabel hM hIndex phase
  intro j l
  rw [GeneralPaperPhysicalScoreMatrix.data true model W depth columns v S hK hCap]
  simpa only [FixedArrayTable.read_ofFn] using score_bound v S hK j l

end Blotto.GeneralPaperRayQueryStorage
