import Blotto.GeneralPaperSourceRepresentativeSortReachedRates

/-! Native source-field materialization retains the complete original
row matrix, selected row/value, returned column and mutable constructor
buffers/frames. Reads share their original row identities and execute no
rational arithmetic. All payload and native work observers are erased. -/
namespace Blotto.GeneralPaperColumnInputStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperEnclosingSourceOwners
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384

def price (W T : ℕ) : ℕ := GeneralPaperNativePayloadFillStorage.workCap W T (64*W)
def scalarCap (W T m : ℕ) : ℕ := T+m+64*W+1
def metadataCap (W T m : ℕ) : ℕ := T+m+price W T+64*W+1
def scalarWindow {T m : ℕ} (W : ℕ) (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (j : Fin m) (i : Fin T) : ℕ :=
  arrayFootprint W rationalWordWidth (rows.read i)+rationalWordWidth ((rows.read i).read j)+
    fields W [T,m,j.val,i.val,64*W]+128*W
def scalarProfile (W T m R : ℕ) : ℕ :=
  arrayProfile W m R+R+5*(natBits (scalarCap W T m)+W)+160*W
def window {T m : ℕ} (W : ℕ) (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (j : Fin m)
    (count : ℕ) (hc : count≤T) : ℕ :=
  rowsFoot W rows+
    GeneralPaperNativePayloadFillStorage.window W rationalWordWidth (fun i => ((rows.read i).read j,64*W))
      (fun i => scalarWindow W rows j i) count hc+
    fields W [T,m,j.val,(GeneralPaperNativeQuantizedMatrix.columnInput (fun w => w) W rows j).2,64*W]+128*W
def profile (W T m R : ℕ) : ℕ :=
  rowsProfile W T m R+
    GeneralPaperNativePayloadFillStorage.profile W R T (64*W) (scalarProfile W T m R)+
    5*(natBits (metadataCap W T m)+W)+160*W

theorem cast_rows_foot {T U m : ℕ} (W : ℕ) (h : T=U) (rows : FixedArrayTable T (FixedArrayTable m ℚ)) :
    rowsFoot W (GeneralPaperRowQuantizer.castRows h rows)=rowsFoot W rows := by
  subst U
  rfl

theorem scalar_bound {T m : ℕ} (W R : ℕ) (rows : FixedArrayTable T (FixedArrayTable m ℚ))
    (h : ∀ i j,rationalWordWidth ((rows.read i).read j)≤R) (j : Fin m) (i : Fin T) :
    scalarWindow W rows j i≤scalarProfile W T m R := by
  have hRow := array_bound W R rationalWordWidth (rows.read i) (h i)
  have hValue := h i j
  have hf := fields_bound W (natBits (scalarCap W T m)) [T,m,j.val,i.val,64*W] (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl
    all_goals unfold scalarCap; omega)
  change fields W _≤5*(natBits (scalarCap W T m)+W)+32*W at hf
  unfold scalarWindow scalarProfile
  omega

theorem work {T m : ℕ} (W : ℕ) (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (j : Fin m)
    (hW : 1≤W) (hIndex : binaryWordWidth (T+1)≤W) :
    (GeneralPaperNativeQuantizedMatrix.columnInput (fun w => w) W rows j).2≤price W T :=
  GeneralPaperNativePayloadFillStorage.prefix_work W (64*W) (fun i => ((rows.read i).read j,64*W))
    (fun _ => le_rfl) hW hIndex T le_rfl

theorem bounded {T m : ℕ} (W R : ℕ) (rows : FixedArrayTable T (FixedArrayTable m ℚ))
    (h : ∀ i j,rationalWordWidth ((rows.read i).read j)≤R)
    (hW : 1≤W) (hIndex : binaryWordWidth (T+1)≤W) (j : Fin m) (count : ℕ) (hc : count≤T) :
    window W rows j count hc≤profile W T m R := by
  have hRows := rows_bound W R rows h
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W R (64*W) (scalarProfile W T m R) rationalWordWidth
    (fun i => ((rows.read i).read j,64*W)) (fun i => scalarWindow W rows j i) (fun i => h i j)
    (fun _ => le_rfl) (fun i => scalar_bound W R rows h j i) hW hIndex count hc
  have hWork := work W rows j hW hIndex
  have hf := fields_bound W (natBits (metadataCap W T m))
    [T,m,j.val,(GeneralPaperNativeQuantizedMatrix.columnInput (fun w => w) W rows j).2,64*W] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change fields W _≤5*(natBits (metadataCap W T m)+W)+32*W at hf
  unfold window profile
  omega

end Blotto.GeneralPaperColumnInputStorage
