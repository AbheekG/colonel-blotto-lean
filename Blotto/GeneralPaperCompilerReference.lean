import Blotto.GeneralPaperEncodedBasisStorage
import Blotto.GeneralPaperSourceRowsStorageContract

/-! A common derived reference word for the retained source/row profile,
two basis-state reservations and every index range used by the complete
local bit-pair price. Calibration uses closed sizes, never a memory census.
This closes those local index premises. Coverage of the remaining compiler
temporaries and their lifetimes is a separate working-space obligation. -/
namespace Blotto.GeneralPaperCompilerReference
open GeneralPaperSourceWordGrowth GeneralPaperReferenceCapacity GeneralPaperReferenceScaling
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def indexSize (m k : ℕ) : ℕ :=
  let p := GeneralPaperProxyParameters.prepare m k
  let T := (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows
  m*(p.K-1)+3+(p.K+1)+(m+1)+(p.S+2)+((p.S+1)*(p.K*p.K)+3)+
    (p.S+4)+(m+p.K+1)+(2*T+p.K+m+1)

noncomputable def profile (C d W : ℕ) (x : Input) : ℕ :=
  GeneralPaperSourceRowsReference.profile C d W x+
    2*GeneralPaperEncodedBasisStorage.paperProfile W x.m x.k+indexSize x.m x.k*W

theorem scaling (C d : ℕ) (x : Input) : Scale (fun W => profile C d W x) := by
  have hs := GeneralPaperSourceRowsReference.scaling C d x
  unfold profile
  fun_prop

noncomputable def width (C d : ℕ) (x : Input) : ℕ :=
  referenceWord (profile C d 1 x)+GeneralPaperPrecallControlWord.word x.m x.k

theorem positive_width (C d : ℕ) (x : Input) : 1≤width C d x := by
  have h := positive (profile C d 1 x)
  unfold width
  omega

theorem control_word (C d : ℕ) (x : Input) : GeneralPaperPrecallControlWord.word x.m x.k≤width C d x := by
  unfold width
  omega

theorem capacity (C d : ℕ) (x : Input) : profile C d (width C d x) x<2^width C d x :=
  padded_profile_capacity (fun W => profile C d W x) (scaling C d x) _

theorem address_word (C d : ℕ) (x : Input) (address : ℕ)
    (h : address≤profile C d (width C d x) x) : binaryWordWidth address≤width C d x :=
  binaryWordWidth_le_of_lt_pow (positive_width C d x) (h.trans_lt (capacity C d x))

theorem index_address (C d : ℕ) (x : Input) (address : ℕ) (h : address≤ indexSize x.m x.k) :
    binaryWordWidth address≤width C d x := by
  apply address_word C d x address
  have hW := Nat.mul_le_mul_left (indexSize x.m x.k) (positive_width C d x)
  unfold profile
  nlinarith only [h,hW,Nat.zero_le (GeneralPaperSourceRowsReference.profile C d (width C d x) x),
    Nat.zero_le (GeneralPaperEncodedBasisStorage.paperProfile (width C d x) x.m x.k)]

theorem local_words (C d : ℕ) (x : Input) :
    let p := GeneralPaperProxyParameters.prepare x.m x.k
    let W := width C d x
    binaryWordWidth (x.m*(p.K-1)+3)≤W ∧
    binaryWordWidth (p.K+1)≤W ∧ binaryWordWidth (x.m+1)≤W ∧
    binaryWordWidth (p.S+2)≤W ∧ binaryWordWidth ((p.S+1)*(p.K*p.K)+3)≤W ∧
    binaryWordWidth (p.S+4)≤W ∧ binaryWordWidth (x.m+p.K+1)≤W ∧
    binaryWordWidth (2*(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows+p.K+x.m+1)≤W := by
  dsimp only
  refine ⟨index_address C d x _ ?_,index_address C d x _ ?_,index_address C d x _ ?_,
    index_address C d x _ ?_,index_address C d x _ ?_,index_address C d x _ ?_,
    index_address C d x _ ?_,index_address C d x _ ?_⟩
  all_goals unfold indexSize; dsimp only [alphabet]; omega

theorem source_capacity {actual : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth actual C d) (x : Input) (first : Bool) :
    GeneralPaperSourceRowsStorageContract.live actual (width C d x) x first<2^width C d x := by
  apply (GeneralPaperSourceRowsStorageContract.live_profile hg _ x first).trans_lt
  apply lt_of_le_of_lt _ (capacity C d x)
  unfold profile
  omega

theorem basis_capacity (C d : ℕ) (x : Input) :
    2*GeneralPaperEncodedBasisStorage.paperProfile (width C d x) x.m x.k<2^width C d x := by
  apply lt_of_le_of_lt _ (capacity C d x)
  unfold profile
  omega

theorem source_basis_capacity {actual : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth actual C d) (x : Input) (first : Bool)
    {j e : ℕ} (left right : GeneralPaperBasisState.State j e)
    (hl : GeneralPaperEncodedBasisStorage.footprint (width C d x) left≤GeneralPaperEncodedBasisStorage.paperProfile (width C d x) x.m x.k)
    (hr : GeneralPaperEncodedBasisStorage.footprint (width C d x) right≤GeneralPaperEncodedBasisStorage.paperProfile (width C d x) x.m x.k) :
    GeneralPaperSourceRowsStorageContract.live actual (width C d x) x first+
      GeneralPaperEncodedBasisStorage.footprint (width C d x) left+
      GeneralPaperEncodedBasisStorage.footprint (width C d x) right<2^width C d x := by
  have hs := GeneralPaperSourceRowsStorageContract.live_profile hg (width C d x) x first
  apply lt_of_le_of_lt _ (capacity C d x)
  unfold profile
  omega

end Blotto.GeneralPaperCompilerReference
