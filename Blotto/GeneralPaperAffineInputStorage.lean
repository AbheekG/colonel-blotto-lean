import Blotto.GeneralPaperSourceEndpointGenerationRates

/-! Native affine-input materialization. Partial reference buffers,
constructor stacks, the current score/two-anchor entry, complete returned
field-list owner, list-copy references and native work counters are counted.
Score matrix and packed point/direction owners belong to the caller. -/
namespace Blotto.GeneralPaperAffineInputStorage
open RationalOrderCell GeneralPaperRayAffine GeneralPaperRayAffineScoreStep
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedReferenceVector
open GeneralPaperAffineWitnessStorage GeneralPaperScoreConstructionStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def entry {m K : ℕ} (W : ℕ) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (j : Fin m) (l : Fin K) : (ℕ×Affine)×ℕ :=
  ((GeneralPaperRayQueryWork.scores matrix j l,
    ⟨GeneralPaperRayAnchorCosts.anchorQ x j l,GeneralPaperRayAnchorCosts.anchorQ w j l⟩),64*W)

def entryFoot (W : ℕ) (a : ℕ×Affine) : ℕ := natBits a.1+affineFoot W a.2+32*W
def entryProfile (W S R : ℕ) : ℕ := natBits S+affineProfile W R+32*W

theorem anchor_height {m K : ℕ} (R : ℕ) (hR : 1≤R) (x : Variable m K → ℚ)
    (hx : ∀ a,RationalHeight (x a) R) (j : Fin m) (l : Fin K) :
    RationalHeight (GeneralPaperRayAnchorCosts.anchorQ x j l) R := by
  unfold GeneralPaperRayAnchorCosts.anchorQ
  split
  · constructor <;> norm_num only [Rat.num_zero,Rat.den_zero,Int.natAbs_zero]
    · exact pow_pos (by decide : 0<2) _
    · exact lt_of_lt_of_le (by decide : 1<2^1) (Nat.pow_le_pow_right (by decide : 1≤2) hR)
  · exact hx _

theorem entry_bound {m K : ℕ} (W S R : ℕ) (hR : 1≤R) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (hs : ∀ j l,((matrix.read j).read l).1≤S) (x w : Variable m K → ℚ)
    (hx : ∀ a,RationalHeight (x a) R) (hw : ∀ a,RationalHeight (w a) R) (j : Fin m) (l : Fin K) :
    entryFoot W (entry W matrix x w j l).1≤entryProfile W S R := by
  have hScore := Nat.add_le_add_left (binaryWordWidth_mono (hs j l)) 1
  have hAffine := affine_bound W R (entry W matrix x w j l).1.2 (anchor_height R hR x hx j l) (anchor_height R hR w hw j l)
  unfold entryFoot entryProfile
  change natBits (GeneralPaperRayQueryWork.scores matrix j l)+affineFoot W (entry W matrix x w j l).1.2+32*W≤_
  unfold natBits GeneralPaperRayQueryWork.scores at *
  omega

theorem field_bound {m K : ℕ} (W S R : ℕ) (hR : 1≤R) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (hs : ∀ j l,((matrix.read j).read l).1≤S) (x w : Variable m K → ℚ)
    (hx : ∀ a,RationalHeight (x a) R) (hw : ∀ a,RationalHeight (w a) R) (j : Fin m) :
    fieldFoot W (GeneralPaperAffineInputPrice.fieldRun (fun w => w) W matrix x w j).1≤fieldProfile W K S R := by
  rw [GeneralPaperAffineInputPrice.field_data]
  have hb := bounded W (entryProfile W S R) (entryFoot W)
    (FixedArrayTable.ofFn (fun l => (entry W matrix x w j l).1)).data (by
      intro i
      simp only [FixedArrayTable.ofFn,Array.getElem_ofFn]
      exact entry_bound W S R hR matrix hs x w hx hw j _)
  change fieldFoot W (FixedArrayTable.ofFn (fun l => (entry W matrix x w j l).1))≤_
  change footprint W (entryFoot W) (FixedArrayTable.ofFn (fun l => (entry W matrix x w j l).1)).data≤_
  have he : K*(entryProfile W S R+W)+64*W=fieldProfile W K S R := by unfold entryProfile fieldProfile; ring
  exact (by simpa only [FixedArrayTable.ofFn,Array.size_ofFn] using hb : footprint W (entryFoot W) _≤_).trans_eq he

def fieldsFoot {K : ℕ} (W : ℕ) (xs : List (Field K)) : ℕ := listFootprint W (fieldFoot W) xs
def listProfile (W m K S R : ℕ) : ℕ := m*(fieldProfile W K S R+2*W)+32*W

theorem fields_bound {m K : ℕ} (W S R : ℕ) (hR : 1≤R) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (hs : ∀ j l,((matrix.read j).read l).1≤S) (x w : Variable m K → ℚ)
    (hx : ∀ a,RationalHeight (x a) R) (hw : ∀ a,RationalHeight (w a) R) :
    fieldsFoot W (GeneralPaperAffineInputPrice.run (fun w => w) W matrix x w).1≤listProfile W m K S R := by
  have he : ∀ field∈(GeneralPaperAffineInputPrice.run (fun w => w) W matrix x w).1,fieldFoot W field≤fieldProfile W K S R := by
    intro field hf
    rw [GeneralPaperAffineInputPrice.data] at hf
    unfold GeneralPaperRayAffineScoreInput.fields at hf
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hf
    simpa only [GeneralPaperAffineInputPrice.field_data] using field_bound W S R hR matrix hs x w hx hw j
  have hh := list_bound W (fieldProfile W K S R) (fieldFoot W) _ he
  simpa only [fieldsFoot,listProfile,GeneralPaperAffineInputPrice.data,GeneralPaperRayAffineScoreInput.fields_length] using hh

def fieldPrice (W K : ℕ) : ℕ := 128*(K+1)*W
def matrixPrice (W m K : ℕ) : ℕ := 256*(m+1)*(K+1)*W
def runPrice (W m K : ℕ) : ℕ := 512*(m+1)*(K+1)*W
def metadataCap (W m K S : ℕ) : ℕ := m+K+S+1+64*W+fieldPrice W K+matrixPrice W m K+runPrice W m K+(8*m+4)*W

def window {m K : ℕ} (W : ℕ) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (outer : ℕ) (ho : outer≤m) (j : Fin m)
    (inner : ℕ) (hi : inner≤K) (l : Fin K) (copied : ℕ) : ℕ :=
  let generated := GeneralPaperAffineInputPrice.matrixRun (fun w => w) W matrix x w
  let inputs := GeneralPaperAffineInputPrice.run (fun w => w) W matrix x w
  reservedFootprint W m (fieldFoot W) (PaperIndexedArrayConstruction.fill (fun w => w) W
      (GeneralPaperAffineInputPrice.fieldRun (fun w => w) W matrix x w) outer ho).1+
    reservedFootprint W K (entryFoot W) (PaperIndexedArrayConstruction.fill (fun w => w) W (entry W matrix x w j) inner hi).1+
    constructorFrames (fun w => w) W W (GeneralPaperAffineInputPrice.fieldRun (fun w => w) W matrix x w) outer ho+
    constructorFrames (fun w => w) W W (entry W matrix x w j) inner hi+
    entryFoot W (entry W matrix x w j l).1+fieldsFoot W inputs.1+
    footprint W (fun _ => 0) generated.1.data+listFootprint W (fun _ => 0) (inputs.1.take copied)+
    GeneralPaperFinRangeStorage.frames W m+
    fields W [m,K,j.val,l.val,l.val-1,GeneralPaperRayQueryWork.scores matrix j l,64*W,
      (GeneralPaperAffineInputPrice.fieldRun (fun w => w) W matrix x w j).2,generated.2,inputs.2,(8*m+4)*W,generated.2+(8*m+4)*W]+256*W

def profile (W m K S R : ℕ) : ℕ :=
  (m*(fieldProfile W K S R+W)+64*W)+fieldProfile W K S R+
    constructorProfile W m (matrixPrice W m K)+constructorProfile W K (fieldPrice W K)+
    entryProfile W S R+listProfile W m K S R+(m*W+64*W)+(m*(2*W)+32*W)+
    (m+1)*(2*(natBits m+W)+160*W)+12*(natBits (metadataCap W m K S)+W)+288*W

theorem bounded {m K : ℕ} (W S R : ℕ) (hR : 1≤R) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (hs : ∀ j l,((matrix.read j).read l).1≤S) (x w : Variable m K → ℚ)
    (hx : ∀ a,RationalHeight (x a) R) (hw : ∀ a,RationalHeight (w a) R)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (outer : ℕ) (ho : outer≤m) (j : Fin m) (inner : ℕ) (hi : inner≤K) (l : Fin K) (copied : ℕ) :
    window W matrix x w outer ho j inner hi l copied≤profile W m K S R := by
  let generated := GeneralPaperAffineInputPrice.matrixRun (fun w => w) W matrix x w
  let inputs := GeneralPaperAffineInputPrice.run (fun w => w) W matrix x w
  have hOuter := indexed_reserved_prefix (fun w => w) W W (fieldProfile W K S R) (fieldFoot W)
    (GeneralPaperAffineInputPrice.fieldRun (fun w => w) W matrix x w) (fun j => field_bound W S R hR matrix hs x w hx hw j) outer ho
  have hInner := indexed_reserved_prefix (fun w => w) W W (entryProfile W S R) (entryFoot W)
    (entry W matrix x w j) (fun l => entry_bound W S R hR matrix hs x w hx hw j l) inner hi
  have hFW := GeneralPaperAffineInputPrice.field_bit_work W matrix x w j hW hK
  have hMW := GeneralPaperAffineInputPrice.matrix_bit_work W matrix x w hW hK hM
  have hLW := GeneralPaperAffineInputPrice.bit_work W matrix x w hW hK hM
  change (GeneralPaperAffineInputPrice.fieldRun (fun w => w) W matrix x w j).2≤fieldPrice W K at hFW
  change generated.2≤matrixPrice W m K at hMW
  change inputs.2≤runPrice W m K at hLW
  have hOC := constructor_bound (fun w => w) W W (matrixPrice W m K)
    (GeneralPaperAffineInputPrice.fieldRun (fun w => w) W matrix x w) hMW outer ho
  have hIC := constructor_bound (fun w => w) W W (fieldPrice W K) (entry W matrix x w j) hFW inner hi
  have hEntry := entry_bound W S R hR matrix hs x w hx hw j l
  have hList := fields_bound W S R hR matrix hs x w hx hw
  change fieldsFoot W inputs.1≤listProfile W m K S R at hList
  have hSlots : footprint W (fun _ => 0) generated.1.data=m*W+64*W := by rw [borrowed,generated.1.size]
  have hLength : inputs.1.length=m := by dsimp only [inputs]; rw [GeneralPaperAffineInputPrice.data,GeneralPaperRayAffineScoreInput.fields_length]
  have hCopy := list_bound W 0 (fun _ => 0) (inputs.1.take copied) (fun _ _ => le_rfl)
  have hCopyLen : (inputs.1.take copied).length≤m := by rw [List.length_take]; exact (Nat.min_le_right _ _).trans_eq hLength
  have hCopyBound : listFootprint W (fun _ => 0) (inputs.1.take copied)≤m*(2*W)+32*W := by
    simpa only [Nat.zero_add] using hCopy.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hCopyLen) _)
  have hFrames := GeneralPaperFinRangeStorage.frames_bound W m
  have hShape : inputs.2=generated.2+(8*m+4)*W := rfl
  have hScore := hs j l
  have hj := j.isLt
  have hl := l.isLt
  have hf := GeneralPaperEncodedScalarStorage.fields_bound W (natBits (metadataCap W m K S))
    [m,K,j.val,l.val,l.val-1,GeneralPaperRayQueryWork.scores matrix j l,64*W,
      (GeneralPaperAffineInputPrice.fieldRun (fun w => w) W matrix x w j).2,generated.2,inputs.2,(8*m+4)*W,generated.2+(8*m+4)*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; change GeneralPaperRayQueryWork.scores matrix j l≤S at hScore; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤12*(natBits (metadataCap W m K S)+W)+32*W at hf
  have he : K*(entryProfile W S R+W)+64*W=fieldProfile W K S R := by unfold entryProfile fieldProfile; ring
  rw [he] at hInner
  unfold window
  dsimp only
  dsimp only [generated,inputs] at hList hSlots hCopyBound hf
  unfold profile
  omega

end Blotto.GeneralPaperAffineInputStorage
