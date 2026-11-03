import Blotto.GeneralPaperEpochInitialConstructionStorage

/-! Four native sparse initial forest arrays create only uniform nodes.
Reserved buffers, constructor frames/controls, complete node/forest returns,
one active node and height-addition scratch are counted without enumerating
the exponentially many represented codes. -/
namespace Blotto.GeneralPaperInitialForestConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperIntervalCache
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def nodeProfile (W height : ℕ) : ℕ := natBits height+natBits 0+16*W

def familyPrefix (W m height count : ℕ) (hc : count≤m) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W m (GeneralPaperSparseNodeBits.footprint W)
    (PaperIndexedArrayConstruction.fill (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m)
      (fun _ : Fin m => (Node.uniform height 0,natBits height+64*W)) count hc).1

theorem family_prefix (W m height count : ℕ) (hc : count≤m) :
    familyPrefix W m height count hc≤m*(nodeProfile W height+W)+64*W :=
  GeneralPaperEncodedReferenceVector.indexed_reserved_prefix (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m)
    W (nodeProfile W height) (GeneralPaperSparseNodeBits.footprint W)
    (fun _ : Fin m => (Node.uniform height 0,natBits height+64*W)) (fun _ => Nat.le_refl _) count hc

theorem family_returned (W m height : ℕ) :
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperSparseNodeBits.footprint W)
      (GeneralPaperForestInitialPrice.family true (fun w => w) W m height).1≤m*(nodeProfile W height+W)+32*W := by
  apply GeneralPaperEncodedFixedVector.bounded
  intro j
  rw [GeneralPaperForestInitialPrice.family,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  exact Nat.le_refl _

def active (W m height count : ℕ) : ℕ := if count<m then nodeProfile W height+natBits height+64*W else 0

def familyWindow (W m height count : ℕ) (hc : count≤m) : ℕ :=
  2*familyPrefix W m height count hc+GeneralPaperGridArrayConstructionStorage.frames W m+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperSparseNodeBits.footprint W)
      (GeneralPaperForestInitialPrice.family true (fun w => w) W m height).1+
    active W m height count+fields W [m,height,count,count+1,m+1,0,1]+256*W

def familyProfile (W m height : ℕ) : ℕ :=
  2*(m*(nodeProfile W height+W)+64*W)+GeneralPaperGridArrayConstructionStorage.frames W m+
    (m*(nodeProfile W height+W)+32*W)+(nodeProfile W height+natBits height+64*W)+
    (7*(natBits (m+1)+natBits (height+1)+W)+32*W)+256*W

theorem family_bounded (W m height count : ℕ) (hc : count≤m) : familyWindow W m height count hc≤familyProfile W m height := by
  have hp := family_prefix W m height count hc
  have hr := family_returned W m height
  have ha : active W m height count≤nodeProfile W height+natBits height+64*W := by
    unfold active
    split
    · exact Nat.le_refl _
    · exact Nat.zero_le _
  have hi := fields_bound W (natBits (m+1)+natBits (height+1)) [m,height,count,count+1,m+1,0,1] (by
    intro x hx
    have hmono := GeneralPaperRankStorageMonotonicity.nat_word
    have h0 := hmono 0 (m+1) (by omega)
    have h1 := hmono 1 (m+1) (by omega)
    have hm := hmono m (m+1) (by omega)
    have hh := hmono height (height+1) (by omega)
    have hj := hmono count (m+1) (by omega)
    have hj1 := hmono (count+1) (m+1) (by omega)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals omega)
  simp only [List.length_cons,List.length_nil] at hi
  unfold familyWindow familyProfile
  omega

theorem family_profile_mono (W m height H : ℕ) (hh : height≤H) : familyProfile W m height≤familyProfile W m H := by
  have hw := GeneralPaperRankStorageMonotonicity.nat_word height H hh
  have hw1 := GeneralPaperRankStorageMonotonicity.nat_word (height+1) (H+1) (Nat.add_le_add_right hh 1)
  unfold familyProfile nodeProfile
  gcongr

def returnedProfile (W m lambda : ℕ) : ℕ := 4*m*nodeProfile W (lambda+1)+4*m*W+64*W

theorem returned (W m lambda : ℕ) :
    GeneralPaperEncodedForestStorage.footprint W (GeneralPaperForestInitialPrice.run true (fun w => w) W m lambda).1≤returnedProfile W m lambda := by
  let trees := (GeneralPaperForestInitialPrice.run true (fun w => w) W m lambda).1
  have hw := GeneralPaperRankStorageMonotonicity.nat_word lambda (lambda+1) (by omega)
  have hj : ∀ j : Fin m, GeneralPaperSparseNodeBits.footprint W (trees.p.read j)+GeneralPaperSparseNodeBits.footprint W (trees.q.read j)+
      GeneralPaperSparseNodeBits.footprint W (trees.lambda.read j)+GeneralPaperSparseNodeBits.footprint W (trees.mu.read j)≤4*nodeProfile W (lambda+1) := by
    intro j
    dsimp only [trees]
    rw [GeneralPaperForestInitialPrice.data]
    simp only [GeneralPaperCatalogueTreeCache.initial,FixedArrayTable.read_ofFn,GeneralPaperSparseNodeBits.footprint,nodeProfile]
    change (natBits lambda+natBits 0+16*W)+(natBits lambda+natBits 0+16*W)+
      (natBits (lambda+1)+natBits 0+16*W)+(natBits (lambda+1)+natBits 0+16*W)≤_
    omega
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hj j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hs
  unfold GeneralPaperEncodedForestStorage.footprint returnedProfile
  dsimp only [trees] at hs
  nlinarith only [hs]

def window (W m lambda count : ℕ) (hc : count≤m) : ℕ :=
  2*familyWindow W m lambda count hc+2*familyWindow W m (lambda+1) count hc+
    GeneralPaperEncodedForestStorage.footprint W (GeneralPaperForestInitialPrice.run true (fun w => w) W m lambda).1+
    fields W [lambda,lambda+1,1]+GeneralPaperNaturalPrimitivePrice.binary (fun w => w) (fun a b => a+b) lambda 1+256*W

def profile (W m lambda : ℕ) : ℕ :=
  4*familyProfile W m (lambda+1)+returnedProfile W m lambda+
    (3*(natBits (lambda+1)+W)+32*W)+2*natBits (lambda+1)+256*W

theorem bounded (W m lambda count : ℕ) (hc : count≤m) : window W m lambda count hc≤profile W m lambda := by
  have hp := (family_bounded W m lambda count hc).trans (family_profile_mono W m lambda (lambda+1) (by omega))
  have hl := family_bounded W m (lambda+1) count hc
  have hr := returned W m lambda
  have hi := fields_bound W (natBits (lambda+1)) [lambda,lambda+1,1] (by
    intro x hx; apply GeneralPaperRankStorageMonotonicity.nat_word
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    all_goals omega)
  have ha := GeneralPaperNaturalPrimitivePrice.binary_le (fun w => w) (fun _ _ h => h) (fun a b => a+b)
    lambda 1 (lambda+1) (by omega) (by omega) (Nat.le_refl _)
  simp only [List.length_cons,List.length_nil] at hi
  change _≤2*natBits (lambda+1) at ha
  unfold window profile
  omega

end Blotto.GeneralPaperInitialForestConstructionStorage
