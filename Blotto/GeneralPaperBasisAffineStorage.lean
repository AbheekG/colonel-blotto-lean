import Blotto.GeneralPaperBasisAffineRHSStorage

/-! Complete native affine cache construction after the last basis stage.
Both full RHS vectors, the two native product windows, full returned affine
cache, determinant copy scratch and twelve parent fields coexist. The
input basis is owned once by the enclosing source window. -/
namespace Blotto.GeneralPaperBasisAffineStorage
open GeneralPaperBasisState GeneralPaperBasisStoredProducts GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
set_option autoImplicit false
set_option maxHeartbeats 9000000
set_option maxRecDepth 8192

def price (model : RationalCostModel) (W d R : ℕ) : ℕ := 2048*(d+1)^2*(W+model.rat R)
def metadataCap (model : RationalCostModel) (W d R : ℕ) : ℕ := d+2+3*price model W d R
def footprint {d : ℕ} (W : ℕ) (cache : GeneralPaperBasisAffineData.Data d) : ℕ :=
  arrayFootprint W integerBits cache.constant+arrayFootprint W integerBits cache.slope+
    integerBits cache.determinant+natBits cache.work+32*W
def controls (d W c s ac bs copy total : ℕ) : List ℕ :=
  [d,c,s,ac,bs,16*W,copy,total,c+s,c+s+ac,c+s+ac+bs,c+s+ac+bs+16*W]

def window {d : ℕ} (model : RationalCostModel) (W cCopied sCopied acCopied bsCopied : ℕ) (state : State d d) : ℕ :=
  let c := GeneralPaperBasisAffineBits.rhsRun model.rat W state false
  let s := GeneralPaperBasisAffineBits.rhsRun model.rat W state true
  let ac := GeneralPaperBasisProductBits.mulVecRun model.rat W state.adjugate c.1
  let bs := GeneralPaperBasisProductBits.mulVecRun model.rat W state.adjugate s.1
  let result := GeneralPaperBasisAffineBits.prepare model.rat W state
  let copy := model.rat (GeneralPaperIntegerPrimitivePrice.word state.determinant)
  arrayFootprint W integerBits c.1+arrayFootprint W integerBits s.1+footprint W result+
    GeneralPaperBasisAffineRHSStorage.window model W cCopied state false+GeneralPaperBasisAffineRHSStorage.window model W sCopied state true+
    GeneralPaperBasisProductStorage.window model W acCopied (fun i k => (state.adjugate.read i).read k) (fun _ => c.1.read)+
    GeneralPaperBasisProductStorage.window model W bsCopied (fun i k => (state.adjugate.read i).read k) (fun _ => s.1.read)+
    copy+fields W (controls d W c.2 s.2 ac.2 bs.2 copy result.work)+256*W
def profile (model : RationalCostModel) (W d R : ℕ) : ℕ :=
  4*arrayProfile W d R+R+natBits (price model W d R)+32*W+
    2*GeneralPaperBasisAffineRHSStorage.profile model W d R+2*GeneralPaperBasisProductStorage.profile model W d R+
    model.rat R+12*(natBits (metadataCap model W d R)+W)+288*W

theorem component_widths (d H C R : ℕ) (hR : GeneralPaperBasisAffineBits.width d H C≤R) :
    1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap d H C)≤R ∧ 1+binaryWordWidth C≤R ∧ 1+binaryWordWidth H≤R := by
  unfold GeneralPaperBasisAffineBits.width at hR
  omega

theorem product_payload {d : ℕ} (model : RationalCostModel) (W H C R : ℕ) (A : IntMatrix d) (v : Vector d)
    (hA : ∀ i k,((A.read i).read k).natAbs≤H) (hv : ∀ i,(v.read i).natAbs≤C)
    (hR : 1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap d H C)≤R) :
    arrayFootprint W integerBits (GeneralPaperBasisProductBits.mulVecRun model.rat W A v).1≤arrayProfile W d R := by
  apply GeneralPaperEncodedBasisStorage.array_bound
  intro i
  rw [GeneralPaperBasisProductBits.mulVecRun,GeneralPaperBasisProductBits.materialize,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  exact GeneralPaperBasisProductStorage.result_word model W H C R _ _ (hA i) hv hR

theorem bounded {d : ℕ} (model : RationalCostModel) (W cCopied sCopied acCopied bsCopied H C R : ℕ) (state : State d d)
    (hA : ∀ i k,((state.adjugate.read i).read k).natAbs≤H) (hDet : state.determinant.natAbs≤H)
    (hConstant : ∀ i,(state.rows.read i).constant.natAbs≤C) (hSlope : ∀ i,(state.rows.read i).slope.natAbs≤C)
    (hR : GeneralPaperBasisAffineBits.width d H C≤R) (hW : 1≤W) (hD : binaryWordWidth (d+1)≤W) :
    window model W cCopied sCopied acCopied bsCopied state≤profile model W d R := by
  let c := GeneralPaperBasisAffineBits.rhsRun model.rat W state false
  let s := GeneralPaperBasisAffineBits.rhsRun model.rat W state true
  let ac := GeneralPaperBasisProductBits.mulVecRun model.rat W state.adjugate c.1
  let bs := GeneralPaperBasisProductBits.mulVecRun model.rat W state.adjugate s.1
  let result := GeneralPaperBasisAffineBits.prepare model.rat W state
  let copy := model.rat (GeneralPaperIntegerPrimitivePrice.word state.determinant)
  have hw := component_widths d H C R hR
  have hc (i) : (c.1.read i).natAbs≤C := by rw [GeneralPaperBasisAffineBits.rhs_data,GeneralPaperBasisAffineData.rhs_read]; exact hConstant i
  have hs (i) : (s.1.read i).natAbs≤C := by rw [GeneralPaperBasisAffineBits.rhs_data,GeneralPaperBasisAffineData.rhs_read]; exact hSlope i
  have hC := GeneralPaperEncodedBasisStorage.array_bound W R integerBits c.1 (fun i => (Nat.add_le_add_left (binaryWordWidth_mono (hc i)) 1).trans hw.2.1)
  have hS := GeneralPaperEncodedBasisStorage.array_bound W R integerBits s.1 (fun i => (Nat.add_le_add_left (binaryWordWidth_mono (hs i)) 1).trans hw.2.1)
  have hAC := product_payload model W H C R state.adjugate c.1 hA hc hw.1
  have hBS := product_payload model W H C R state.adjugate s.1 hA hs hw.1
  change arrayFootprint W integerBits ac.1≤arrayProfile W d R at hAC
  change arrayFootprint W integerBits bs.1≤arrayProfile W d R at hBS
  have hDetWord : integerBits state.determinant≤R := (Nat.add_le_add_left (binaryWordWidth_mono hDet) 1).trans hw.2.2
  have hCopy : copy≤model.rat R := model.monotone hDetWord
  have hRC := GeneralPaperBasisAffineRHSStorage.bounded model W cCopied C R state false hConstant hw.2.1 hW hD
  have hRS := GeneralPaperBasisAffineRHSStorage.bounded model W sCopied C R state true hSlope hw.2.1 hW hD
  have hPC := GeneralPaperBasisProductStorage.bounded model W acCopied H C R
    (fun i k => (state.adjugate.read i).read k) (fun _ => c.1.read) hA (fun _ => hc) hw.1 hW hD
  have hPS := GeneralPaperBasisProductStorage.bounded model W bsCopied H C R
    (fun i k => (state.adjugate.read i).read k) (fun _ => s.1.read) hA (fun _ => hs) hw.1 hW hD
  have hWork := (GeneralPaperBasisAffineBits.work model.rat model.monotone W H C hW hD state hA hDet hConstant hSlope).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hR) W))
  change result.work≤price model W d R at hWork
  have hWorkWord : natBits result.work≤natBits (price model W d R) := Nat.add_le_add_left (binaryWordWidth_mono hWork) 1
  have hShape : result.work=c.2+s.2+ac.2+bs.2+16*W+copy := rfl
  have hf := fields_bound W (natBits (metadataCap model W d R)) (controls d W c.2 s.2 ac.2 bs.2 copy result.work) (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at ha
    unfold metadataCap
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤12*(natBits (metadataCap model W d R)+W)+32*W at hf
  have hCache : footprint W result≤2*arrayProfile W d R+R+natBits (price model W d R)+32*W := by
    change arrayFootprint W integerBits ac.1+arrayFootprint W integerBits bs.1+integerBits state.determinant+natBits result.work+32*W≤_
    omega
  unfold window profile
  dsimp only
  dsimp only [c,s,ac,bs,result,copy] at hC hS hCache hRC hRS hPC hPS hCopy hf
  omega

end Blotto.GeneralPaperBasisAffineStorage
