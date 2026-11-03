import Blotto.GeneralPaperCataloguePointStorage
import Blotto.GeneralPaperNativeNatFillStorage

/-! Native snapshot-prefix construction. The input conversion cursor,
running-total recursion, returned prefix list, reserved packing buffers and
full returned array coexist conservatively. These observers erase; the
algorithm still performs one running scan and one materialization. -/
namespace Blotto.GeneralPaperEpochPrefixConstructionStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

def cursor {n : ℕ} (W used : ℕ) (values : FixedArrayTable n ℕ) : ℕ :=
  let s := StoredArrayReferenceList.advance values.data used ⟨values.data.size,Nat.le_refl _,[]⟩
  fields W [s.remaining]+listFootprint W natBits s.tail+64*W

theorem cursor_bound {n : ℕ} (W cap used : ℕ) (values : FixedArrayTable n ℕ)
    (hv : ∀ r,values.read r≤cap) : cursor W used values≤n*(natBits cap+2*W)+natBits n+129*W := by
  let s := StoredArrayReferenceList.advance values.data used ⟨values.data.size,Nat.le_refl _,[]⟩
  have hm := StoredArrayReferenceList.advance_mass values.data used ⟨values.data.size,Nat.le_refl _,[]⟩
  change s.remaining+s.tail.length=values.data.size+0 at hm
  rw [values.size] at hm
  have ht := list_bound W (natBits cap) natBits s.tail (by
    intro x hx
    exact Nat.add_le_add_left (binaryWordWidth_mono
      (GeneralPaperEpochPointExecution.member_bound cap values hv x
        (GeneralPaperCataloguePointStorage.cursor_members values.data used x hx))) 1)
  have hl := Nat.mul_le_mul_right (natBits cap+2*W) (show s.tail.length≤n by omega)
  have hr : natBits s.remaining≤natBits n := Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1
  dsimp only [s] at ht hl hr
  unfold cursor fields
  dsimp only
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  omega

def scanFrames (model : RationalCostModel) (W total : ℕ) : List ℕ → ℕ
  | [] => fields W [total]+64*W
  | value::rest => fields W [total,value,total+value]+
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) total value+96*W+
      scanFrames model W (total+value) rest

theorem scan_frames (model : RationalCostModel) (W cap L total : ℕ) (values : List ℕ)
    (ht : total+values.sum≤cap) (hw : natBits cap≤L) :
    scanFrames model W total values≤(values.length+1)*(3*(natBits cap+W)+2*model.rat L+128*W) := by
  induction values generalizing total with
  | nil =>
    have hf := fields_bound W (natBits cap) [total] (by
      intro x hx
      have he : x=total := by simpa only [List.mem_singleton] using hx
      rw [he]
      exact Nat.add_le_add_left (binaryWordWidth_mono (by simpa using ht)) 1)
    simp only [List.length_singleton,Nat.one_mul] at hf
    change fields W [total]+64*W≤(0+1)*(3*(natBits cap+W)+2*model.rat L+128*W)
    omega
  | cons value rest ih =>
    have ht' : total+value+rest.sum≤cap := by simpa only [List.sum_cons,Nat.add_assoc] using ht
    have hf := fields_bound W (natBits cap) [total,value,total+value] (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl <;>
        exact Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1)
    change fields W [total,value,total+value]≤3*(natBits cap+W)+32*W at hf
    have hp := (GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b)
      total value cap (by omega) (by omega) (by omega)).trans
        (Nat.mul_le_mul_left 2 (model.monotone hw))
    have hi := ih (total+value) ht'
    rw [scanFrames,List.length_cons]
    nlinarith only [hf,hp,hi]

def window {n : ℕ} (model : RationalCostModel) (W used copied : ℕ) (values : FixedArrayTable n ℕ) : ℕ :=
  let input := StoredArrayReferenceList.list values.data
  let result := (GeneralPaperEpochPrefixPrice.scan model.rat W 0 input).1
  GeneralPaperEncodedNatArray.footprint W values+cursor W used values+
    listFootprint W natBits input+2*listFootprint W natBits result+scanFrames model W 0 input+
    GeneralPaperGridArrayConstructionStorage.packingWindow W copied result+
    GeneralPaperEncodedNatArray.footprint W (GeneralPaperEpochPrefixPrice.run true (fun w => w) model.rat W values).1+
    fields W [n,n+1,n+2]+256*W

def profile (model : RationalCostModel) (W cap L n : ℕ) : ℕ :=
  n*(natBits cap+W)+32*W+(n*(natBits cap+2*W)+natBits n+129*W)+
    (n*(natBits cap+2*W)+32*W)+2*((n+1)*(natBits cap+2*W)+32*W)+
    (n+1)*(3*(natBits cap+W)+2*model.rat L+128*W)+
    ((n+1)*(natBits cap+2*W)+32*W+2*((n+1)*(natBits cap+W)+64*W)+
      GeneralPaperGridArrayConstructionStorage.frames W (n+1)+128*W)+
    ((n+1)*(natBits cap+W)+32*W)+3*(natBits (n+2)+W)+288*W

def shortProfile (model : RationalCostModel) (W H n : ℕ) : ℕ :=
  n*(H+W)+32*W+(n*(H+2*W)+natBits n+129*W)+
    (n*(H+2*W)+32*W)+2*((n+1)*(H+2*W)+32*W)+
    (n+1)*(3*(H+W)+2*model.rat H+128*W)+
    ((n+1)*(H+2*W)+32*W+2*((n+1)*(H+W)+64*W)+
      GeneralPaperGridArrayConstructionStorage.frames W (n+1)+128*W)+
    ((n+1)*(H+W)+32*W)+3*(natBits (n+2)+W)+288*W


theorem profile_short (model : RationalCostModel) (W cap H n : ℕ) (hw : natBits cap≤H) :
    profile model W cap H n≤shortProfile model W H n := by
  unfold profile shortProfile
  gcongr

theorem returned_bound {n : ℕ} (model : RationalCostModel) (W cap H : ℕ) (values : FixedArrayTable n ℕ)
    (ht : values.data.toList.sum≤cap) (hw : natBits cap≤H) :
    GeneralPaperEncodedNatArray.footprint W (GeneralPaperEpochPrefixPrice.run true (fun w => w) model.rat W values).1≤
      (n+1)*(H+W)+32*W := by
  apply GeneralPaperEncodedNatArray.bounded
  intro r
  rw [GeneralPaperEpochPrefixPrice.data,GeneralPaperEpochPrefixArray.read_build]
  have he := congrArg List.sum (List.take_append_drop r.val values.data.toList)
  rw [List.sum_append] at he
  exact (Nat.add_le_add_left (binaryWordWidth_mono (show (values.data.toList.take r.val).sum≤cap by omega)) 1).trans hw

theorem bounded {n : ℕ} (model : RationalCostModel) (W cap L used copied : ℕ)
    (values : FixedArrayTable n ℕ) (hv : ∀ r,values.read r≤cap)
    (ht : values.data.toList.sum≤cap) (hw : natBits cap≤L) :
    window model W used copied values≤profile model W cap L n := by
  let input := StoredArrayReferenceList.list values.data
  let result := (GeneralPaperEpochPrefixPrice.scan model.rat W 0 input).1
  have hlen : input.length=n := by simp only [input,StoredArrayReferenceList.list_data,Array.length_toList,values.size]
  have htotal : 0+input.sum≤cap := by simpa only [input,StoredArrayReferenceList.list_data,Nat.zero_add] using ht
  have hinput : ∀ x∈input,x≤cap := by
    intro x hx
    exact GeneralPaperEpochPointExecution.member_bound cap values hv x
      (by simpa only [input,StoredArrayReferenceList.list_data] using hx)
  have hresult : ∀ x∈result,x≤cap := GeneralPaperEpochPrefixPrice.scan_bounds model.rat W cap 0 input htotal
  have hrlen : result.length=n+1 := by rw [GeneralPaperEpochPrefixPrice.scan_length,hlen]
  have ha := GeneralPaperEncodedNatArray.bounded W (natBits cap) values
    (fun r => Nat.add_le_add_left (binaryWordWidth_mono (hv r)) 1)
  have hc := cursor_bound W cap used values hv
  have hi := list_bound W (natBits cap) natBits input
    (fun x hx => Nat.add_le_add_left (binaryWordWidth_mono (hinput x hx)) 1)
  rw [hlen] at hi
  have hr := list_bound W (natBits cap) natBits result
    (fun x hx => Nat.add_le_add_left (binaryWordWidth_mono (hresult x hx)) 1)
  rw [hrlen] at hr
  have hs := scan_frames model W cap L 0 input htotal hw
  rw [hlen] at hs
  have hp := GeneralPaperGridArrayConstructionStorage.packing_window W cap copied result hresult
  rw [hrlen] at hp
  have hout := GeneralPaperEncodedNatArray.bounded W (natBits cap)
    (GeneralPaperEpochPrefixPrice.run true (fun w => w) model.rat W values).1 (by
      intro r
      rw [GeneralPaperEpochPrefixPrice.data]
      rw [GeneralPaperEpochPrefixArray.read_build]
      have he := congrArg List.sum (List.take_append_drop r.val values.data.toList)
      rw [List.sum_append] at he
      exact Nat.add_le_add_left (binaryWordWidth_mono (show (values.data.toList.take r.val).sum≤cap by omega)) 1)
  have hf := fields_bound W (natBits (n+2)) [n,n+1,n+2] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> exact Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1)
  change fields W [n,n+1,n+2]≤3*(natBits (n+2)+W)+32*W at hf
  dsimp only [window,profile]
  dsimp only [input,result] at hi hr hs hp
  omega

end Blotto.GeneralPaperEpochPrefixConstructionStorage
