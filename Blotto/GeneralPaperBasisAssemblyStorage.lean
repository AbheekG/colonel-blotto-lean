import Blotto.GeneralPaperBasisDivideStorage

/-! Literal point/direction assembly branch storage. Prefix references,
fresh original-grid tail divisions, prefix negations and one/zero constants
are counted with actual guarded scratch, native fields and full arrays. -/
namespace Blotto.GeneralPaperBasisAssemblyStorage
open GeneralPaperBasisStoredProducts GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile array_bound)
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem tail_words {d : ℕ} (N R : ℕ) (initial : Vector d) (hi : ∀ i,(initial.read i).natAbs≤N)
    (hR : 1+4*binaryWordWidth N≤R) (k : Fin d) :
    rationalWordWidth (initial.read k:ℚ)≤R ∧ rationalWordWidth (N:ℚ)≤R ∧
    rationalWordWidth ((initial.read k:ℚ)/(N:ℚ))≤R ∧ integerBits (initial.read k)≤R ∧ natBits N≤R := by
  have hu := GeneralPaperBasisStageSize.int_height (initial.read k) N (hi k)
  have hn := GeneralPaperBasisDivideBits.nat_height N
  have hU := rationalWordWidth_of_height hu
  have hN := rationalWordWidth_of_height hn
  have hV := rationalWordWidth_of_height (hu.div hn)
  have hI := binaryWordWidth_mono (hi k)
  unfold integerBits natBits
  omega

theorem point_word {j d : ℕ} (model : RationalCostModel) (W N R : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j)
    (initial : Vector d) (hp : ∀ i,rationalWordWidth (first.read i)≤R) (hi : ∀ i,(initial.read i).natAbs≤N)
    (hR : 1+4*binaryWordWidth N≤R) (k : Fin d) :
    rationalWordWidth (GeneralPaperBasisAssemblyBits.pointScalar model.rat W N first initial k).1≤R := by
  unfold GeneralPaperBasisAssemblyBits.pointScalar
  split
  · exact hp _
  · exact (tail_words N R initial hi hR k).2.2.1

def pointPrice (model : RationalCostModel) (W R : ℕ) : ℕ := 32*W+4*model.rat R
def pointCap (model : RationalCostModel) (W j d R : ℕ) : ℕ := j+d+1+3*pointPrice model W R+32*W
def pointBranch {j d : ℕ} (model : RationalCostModel) (W N : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j) (initial : Vector d) (k : Fin d) : ℕ :=
  if h : k.val<j then rationalWordWidth (first.read ⟨k.val,h⟩) else
    let u := (initial.read k:ℚ)
    let n := (N:ℚ)
    let castU := model.rat (rationalWordWidth u)
    let castN := model.rat (rationalWordWidth n)
    let div := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) u n
    rationalWordWidth u+rationalWordWidth n+integerBits (initial.read k)+natBits N+castU+castN+div+
      fields W [castU,castN,div,32*W+castU,32*W+castU+castN,32*W+castU+castN+div]+128*W
def pointScalarWindow {j d : ℕ} (model : RationalCostModel) (W N : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j) (initial : Vector d) (k : Fin d) : ℕ :=
  let result := GeneralPaperBasisAssemblyBits.pointScalar model.rat W N first initial k
  rationalWordWidth result.1+fields W [j,d,k.val,result.2,16*W,32*W]+128*W+pointBranch model W N first initial k
def pointScalarProfile (model : RationalCostModel) (W j d R : ℕ) : ℕ :=
  5*R+4*model.rat R+12*(natBits (pointCap model W j d R)+W)+320*W

theorem point_scalar_bound {j d : ℕ} (model : RationalCostModel) (W N R : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j)
    (initial : Vector d) (hp : ∀ i,rationalWordWidth (first.read i)≤R) (hi : ∀ i,(initial.read i).natAbs≤N)
    (hR : 1+4*binaryWordWidth N≤R) (k : Fin d) : pointScalarWindow model W N first initial k≤pointScalarProfile model W j d R := by
  let result := GeneralPaperBasisAssemblyBits.pointScalar model.rat W N first initial k
  have hWord := point_word model W N R first initial hp hi hR k
  have hWork := (GeneralPaperBasisAssemblyBits.point_scalar_work model.rat model.monotone W N first initial hi k).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left 4 (model.monotone hR)) (32*W))
  change result.2≤pointPrice model W R at hWork
  have hFields := fields_bound W (natBits (pointCap model W j d R)) [j,d,k.val,result.2,16*W,32*W] (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold pointCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤6*(natBits (pointCap model W j d R)+W)+32*W at hFields
  have hBranch : pointBranch model W N first initial k≤4*R+4*model.rat R+6*(natBits (pointCap model W j d R)+W)+160*W := by
    unfold pointBranch
    split
    · have h := hp ⟨k.val,by assumption⟩; omega
    · dsimp only
      have ht := tail_words N R initial hi hR k
      let castU := model.rat (rationalWordWidth (initial.read k:ℚ))
      let castN := model.rat (rationalWordWidth (N:ℚ))
      let div := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (initial.read k:ℚ) (N:ℚ)
      have hU := model.monotone ht.1
      have hN := model.monotone ht.2.1
      have hDiv := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) (initial.read k:ℚ) (N:ℚ) R ht.1 ht.2.1 ht.2.2.1
      have hf := fields_bound W (natBits (pointCap model W j d R))
        [castU,castN,div,32*W+castU,32*W+castU+castN,32*W+castU+castN+div] (by
          intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
          simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
          all_goals unfold pointCap pointPrice; dsimp only [castU,castN,div]; omega)
      change GeneralPaperEncodedScalarStorage.fields W _≤6*(natBits (pointCap model W j d R)+W)+32*W at hf
      dsimp only [castU,castN,div] at hf
      omega
  unfold pointScalarWindow pointScalarProfile
  dsimp only
  dsimp only [result] at hFields
  omega

def pointCallerCap (model : RationalCostModel) (W j d R : ℕ) : ℕ := j+d+1+3*GeneralPaperNativePayloadFillStorage.workCap W d (pointPrice model W R)+32*W
def pointWindow {j d : ℕ} (model : RationalCostModel) (W copied N : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j) (initial : Vector d) : ℕ :=
  let result := GeneralPaperBasisAssemblyBits.pointRun model.rat W N first initial
  arrayFootprint W rationalWordWidth first+natBits N+
    GeneralPaperNativePayloadFillStorage.window W rationalWordWidth (GeneralPaperBasisAssemblyBits.pointScalar model.rat W N first initial)
      (pointScalarWindow model W N first initial) (min copied d) (Nat.min_le_right _ _)+fields W [j,d,result.2,32*W]+128*W
def pointProfile (model : RationalCostModel) (W j d R : ℕ) : ℕ := arrayProfile W j R+R+
  GeneralPaperNativePayloadFillStorage.profile W R d (pointPrice model W R) (pointScalarProfile model W j d R)+
    4*(natBits (pointCallerCap model W j d R)+W)+160*W

theorem point_bound {j d : ℕ} (model : RationalCostModel) (W copied N R : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j)
    (initial : Vector d) (hp : ∀ i,rationalWordWidth (first.read i)≤R) (hi : ∀ i,(initial.read i).natAbs≤N)
    (hR : 1+4*binaryWordWidth N≤R) (hW : 1≤W) (hIndex : binaryWordWidth (d+1)≤W) :
    pointWindow model W copied N first initial≤pointProfile model W j d R := by
  have hFirst := array_bound W R rationalWordWidth first hp
  have hN : natBits N≤R := by unfold natBits; omega
  have hC (k) : (GeneralPaperBasisAssemblyBits.pointScalar model.rat W N first initial k).2≤pointPrice model W R :=
    (GeneralPaperBasisAssemblyBits.point_scalar_work model.rat model.monotone W N first initial hi k).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left 4 (model.monotone hR)) (32*W))
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W R (pointPrice model W R) (pointScalarProfile model W j d R) rationalWordWidth
    (GeneralPaperBasisAssemblyBits.pointScalar model.rat W N first initial) (pointScalarWindow model W N first initial)
    (point_word model W N R first initial hp hi hR) hC (point_scalar_bound model W N R first initial hp hi hR)
    hW hIndex (min copied d) (Nat.min_le_right _ _)
  have hWork := GeneralPaperNativePayloadFillStorage.prefix_work W (pointPrice model W R)
    (GeneralPaperBasisAssemblyBits.pointScalar model.rat W N first initial) hC hW hIndex d le_rfl
  change (GeneralPaperBasisAssemblyBits.pointRun model.rat W N first initial).2≤GeneralPaperNativePayloadFillStorage.workCap W d (pointPrice model W R) at hWork
  have hf := fields_bound W (natBits (pointCallerCap model W j d R)) [j,d,(GeneralPaperBasisAssemblyBits.pointRun model.rat W N first initial).2,32*W] (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl
    all_goals unfold pointCallerCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (pointCallerCap model W j d R)+W)+32*W at hf
  unfold pointWindow pointProfile
  dsimp only
  omega

theorem direction_word {j d : ℕ} (model : RationalCostModel) (W s R : ℕ) (hs : 1≤s)
    (first : GeneralPaperBasisRationalSolve.RatVector j) (hp : ∀ i,RationalHeight (first.read i) s)
    (hR : 1+2*s≤R) (k : Fin d) : rationalWordWidth (GeneralPaperBasisAssemblyBits.directionScalar model.rat W first k).1≤R := by
  unfold GeneralPaperBasisAssemblyBits.directionScalar
  split
  · exact (rationalWordWidth_of_height (hp _).neg).trans hR
  · split
    · exact (rationalWordWidth_of_height ((GeneralPaperBasisDivideBits.nat_height 1).mono (by exact hs))).trans hR
    · exact (rationalWordWidth_of_height (GeneralPaperQuantizedHeight.zero_height s (by omega))).trans hR

def directionPrice (model : RationalCostModel) (W R : ℕ) : ℕ := 32*W+2*model.rat R
def directionCap (model : RationalCostModel) (W j d R : ℕ) : ℕ := j+d+1+3*directionPrice model W R+32*W
def directionBranch {j d : ℕ} (model : RationalCostModel) (W : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j) (k : Fin d) : ℕ :=
  if h : k.val<j then
    let neg := GeneralPaperRationalPrimitivePrice.unary model.rat (fun a => -a) (first.read ⟨k.val,h⟩)
    rationalWordWidth (first.read ⟨k.val,h⟩)+neg+fields W [neg,32*W+neg]+128*W
  else
    let cast := model.rat (rationalWordWidth (if k.val=j then (1:ℚ) else 0))
    cast+fields W [cast,16*W+cast]+128*W
def directionScalarWindow {j d : ℕ} (model : RationalCostModel) (W : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j) (k : Fin d) : ℕ :=
  let result := GeneralPaperBasisAssemblyBits.directionScalar model.rat W first k
  rationalWordWidth result.1+fields W [j,d,k.val,result.2,16*W,32*W]+128*W+directionBranch model W first k
def directionScalarProfile (model : RationalCostModel) (W j d R : ℕ) : ℕ :=
  2*R+2*model.rat R+8*(natBits (directionCap model W j d R)+W)+320*W

theorem direction_scalar_bound {j d : ℕ} (model : RationalCostModel) (W s R : ℕ) (hs : 1≤s)
    (first : GeneralPaperBasisRationalSolve.RatVector j) (hp : ∀ i,RationalHeight (first.read i) s)
    (hR : 1+2*s≤R) (k : Fin d) : directionScalarWindow model W first k≤directionScalarProfile model W j d R := by
  let result := GeneralPaperBasisAssemblyBits.directionScalar model.rat W first k
  have hWord := direction_word model W s R hs first hp hR k
  have hWork := (GeneralPaperBasisAssemblyBits.direction_scalar_work model.rat model.monotone W s hs first hp k).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (model.monotone hR)) (32*W))
  change result.2≤directionPrice model W R at hWork
  have hFields := fields_bound W (natBits (directionCap model W j d R)) [j,d,k.val,result.2,16*W,32*W] (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold directionCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤6*(natBits (directionCap model W j d R)+W)+32*W at hFields
  have hBranch : directionBranch model W first k≤R+2*model.rat R+2*(natBits (directionCap model W j d R)+W)+160*W := by
    unfold directionBranch
    split
    · rename_i hk
      dsimp only
      let neg := GeneralPaperRationalPrimitivePrice.unary model.rat (fun a => -a) (first.read ⟨k.val,hk⟩)
      have hA := (rationalWordWidth_of_height (hp ⟨k.val,hk⟩)).trans hR
      have hN := (rationalWordWidth_of_height (hp ⟨k.val,hk⟩).neg).trans hR
      have hNeg := GeneralPaperRationalPrimitivePrice.unary_le model.rat model.monotone (fun a => -a) (first.read ⟨k.val,hk⟩) R hA hN
      have hf := fields_bound W (natBits (directionCap model W j d R)) [neg,32*W+neg] (by
        intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl|rfl
        all_goals unfold directionCap directionPrice; dsimp only [neg]; omega)
      change GeneralPaperEncodedScalarStorage.fields W _≤2*(natBits (directionCap model W j d R)+W)+32*W at hf
      dsimp only [neg] at hf
      omega
    · dsimp only
      have hConst : rationalWordWidth (if k.val=j then (1:ℚ) else 0)≤R := by
        split
        · exact (rationalWordWidth_of_height ((GeneralPaperBasisDivideBits.nat_height 1).mono (by exact hs))).trans hR
        · exact (rationalWordWidth_of_height (GeneralPaperQuantizedHeight.zero_height s (by omega))).trans hR
      let cast := model.rat (rationalWordWidth (if k.val=j then (1:ℚ) else 0))
      have hCast := model.monotone hConst
      have hf := fields_bound W (natBits (directionCap model W j d R)) [cast,16*W+cast] (by
        intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl|rfl
        all_goals unfold directionCap directionPrice; dsimp only [cast]; omega)
      change GeneralPaperEncodedScalarStorage.fields W _≤2*(natBits (directionCap model W j d R)+W)+32*W at hf
      dsimp only [cast] at hf
      omega
  unfold directionScalarWindow directionScalarProfile
  dsimp only
  dsimp only [result] at hFields
  omega

def directionCallerCap (model : RationalCostModel) (W j d R : ℕ) : ℕ := j+d+1+3*GeneralPaperNativePayloadFillStorage.workCap W d (directionPrice model W R)+16*W
def directionWindow {j d : ℕ} (model : RationalCostModel) (W copied : ℕ) (first : GeneralPaperBasisRationalSolve.RatVector j) : ℕ :=
  let result := GeneralPaperBasisAssemblyBits.directionRun (d:=d) model.rat W first
  arrayFootprint W rationalWordWidth first+
    GeneralPaperNativePayloadFillStorage.window W rationalWordWidth (GeneralPaperBasisAssemblyBits.directionScalar model.rat W first : Fin d → ℚ×ℕ)
      (directionScalarWindow model W first) (min copied d) (Nat.min_le_right _ _)+fields W [j,d,result.2,16*W]+128*W
def directionProfile (model : RationalCostModel) (W j d R : ℕ) : ℕ := arrayProfile W j R+
  GeneralPaperNativePayloadFillStorage.profile W R d (directionPrice model W R) (directionScalarProfile model W j d R)+
    4*(natBits (directionCallerCap model W j d R)+W)+160*W

theorem direction_bound {j d : ℕ} (model : RationalCostModel) (W copied s R : ℕ) (hs : 1≤s)
    (first : GeneralPaperBasisRationalSolve.RatVector j) (hp : ∀ i,RationalHeight (first.read i) s)
    (hR : 1+2*s≤R) (hW : 1≤W) (hIndex : binaryWordWidth (d+1)≤W) :
    directionWindow (d:=d) model W copied first≤directionProfile model W j d R := by
  have hFirst := array_bound W R rationalWordWidth first (fun i => (rationalWordWidth_of_height (hp i)).trans hR)
  have hC (k : Fin d) : (GeneralPaperBasisAssemblyBits.directionScalar model.rat W first k).2≤directionPrice model W R :=
    (GeneralPaperBasisAssemblyBits.direction_scalar_work model.rat model.monotone W s hs first hp k).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (model.monotone hR)) (32*W))
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W R (directionPrice model W R) (directionScalarProfile model W j d R) rationalWordWidth
    (GeneralPaperBasisAssemblyBits.directionScalar model.rat W first) (directionScalarWindow model W first)
    (direction_word model W s R hs first hp hR) hC (direction_scalar_bound model W s R hs first hp hR)
    hW hIndex (min copied d) (Nat.min_le_right _ _)
  have hWork := GeneralPaperNativePayloadFillStorage.prefix_work W (directionPrice model W R)
    (GeneralPaperBasisAssemblyBits.directionScalar model.rat W first : Fin d → ℚ×ℕ) hC hW hIndex d le_rfl
  change (GeneralPaperBasisAssemblyBits.directionRun (d:=d) model.rat W first).2≤GeneralPaperNativePayloadFillStorage.workCap W d (directionPrice model W R) at hWork
  have hf := fields_bound W (natBits (directionCallerCap model W j d R)) [j,d,(GeneralPaperBasisAssemblyBits.directionRun (d:=d) model.rat W first).2,16*W] (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl
    all_goals unfold directionCallerCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (directionCallerCap model W j d R)+W)+32*W at hf
  unfold directionWindow directionProfile
  dsimp only
  omega

end Blotto.GeneralPaperBasisAssemblyStorage
