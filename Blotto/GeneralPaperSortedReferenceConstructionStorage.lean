import Blotto.GeneralPaperSharedCacheConstructionStorage

/-! The actual sort-plus-reference-materialization row constructor.
Source rational owners coexist with order sorting, full indexed-fill
buffers/frames and callback/parent scalar fields. Output references borrow
the retained source values, whose origins are already checked. -/
namespace Blotto.GeneralPaperSortedReferenceConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

def callback {R : ℕ} (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable R ℚ)
    (a : Fin R) : ℚ×ℕ :=
  (values.read ((GeneralPaperNativeRepresentativeSort.run model.rat (fun w => w) W values).1.read a),64*W)

def scalar {R : ℕ} (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable R ℚ) (a : Fin R) : ℕ :=
  let j := (GeneralPaperNativeRepresentativeSort.run model.rat (fun w => w) W values).1.read a
  fields W [a.val,j.val,64*W]+96*W

def scalarProfile (W R : ℕ) : ℕ := 3*(natBits (R+64*W+1)+W)+128*W

theorem scalar_bound {R : ℕ} (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable R ℚ) (a : Fin R) :
    scalar model W values a≤scalarProfile W R := by
  let j := (GeneralPaperNativeRepresentativeSort.run model.rat (fun w => w) W values).1.read a
  have ha := a.isLt.le
  have hj := j.isLt.le
  have hf := fields_bound W (natBits (R+64*W+1)) [a.val,j.val,64*W] (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl <;> omega)
  change fields W _≤3*(natBits (R+64*W+1)+W)+32*W at hf
  unfold scalar scalarProfile
  change fields W [a.val,j.val,64*W]+96*W≤_
  omega

def price (model : RationalCostModel) (W R H : ℕ) : ℕ :=
  GeneralPaperRepresentativeSortStorage.price model W R H+
    GeneralPaperNativePayloadFillStorage.workCap W R (64*W)+16*W
def cap (model : RationalCostModel) (W R H : ℕ) : ℕ := R+price model W R H+64*W+1

def window {R : ℕ} (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable R ℚ)
    (used copied count : ℕ) (hc : count≤R) (active : Option (Fin R×Fin R)) : ℕ :=
  let order := GeneralPaperNativeRepresentativeSort.run model.rat (fun w => w) W values
  let stored := PaperIndexedArrayConstruction.run (fun w => w) W (callback model W values)
  let made := GeneralPaperNativeSortedRows.one model.rat (fun w => w) W values
  GeneralPaperRepresentativeSortStorage.window model W values used copied active+
    GeneralPaperNativePayloadFillStorage.window W (fun _ : ℚ => 0) (callback model W values) (scalar model W values) count hc+
    fields W [R,order.2,stored.2,order.2+stored.2,16*W,made.2]+128*W

def profile (model : RationalCostModel) (W R H : ℕ) : ℕ :=
  GeneralPaperRepresentativeSortStorage.profile model W R H+
    GeneralPaperNativePayloadFillStorage.profile W 0 R (64*W) (scalarProfile W R)+
    6*(natBits (cap model W R H)+W)+160*W

theorem work {R : ℕ} (model : RationalCostModel) (W H : ℕ) (values : FixedArrayTable R ℚ)
    (hv : ∀ j,rationalWordWidth (values.read j)≤H) (hW : 1≤W) (hIndex : binaryWordWidth (R+1)≤W) :
    (GeneralPaperNativeSortedRows.one model.rat (fun w => w) W values).2≤price model W R H := by
  have hs := GeneralPaperRepresentativeSortStorage.work model W H values hv hW hIndex
  have hf := GeneralPaperNativePayloadFillStorage.prefix_work W (64*W) (callback model W values)
    (fun _ => le_rfl) hW hIndex R le_rfl
  change (PaperIndexedArrayConstruction.run (fun w => w) W (callback model W values)).2≤
    GeneralPaperNativePayloadFillStorage.workCap W R (64*W) at hf
  change (GeneralPaperNativeRepresentativeSort.run model.rat (fun w => w) W values).2+
    (PaperIndexedArrayConstruction.run (fun w => w) W (callback model W values)).2+16*W≤_
  unfold price
  omega

theorem bounded {R : ℕ} (model : RationalCostModel) (W H : ℕ) (values : FixedArrayTable R ℚ)
    (hv : ∀ j,rationalWordWidth (values.read j)≤H) (hW : 1≤W) (hIndex : binaryWordWidth (R+1)≤W)
    (used copied count : ℕ) (hc : count≤R) (active : Option (Fin R×Fin R)) :
    window model W values used copied count hc active≤profile model W R H := by
  have hs := GeneralPaperRepresentativeSortStorage.bounded model W H values hv hW hIndex used copied active
  have hf := GeneralPaperNativePayloadFillStorage.bounded W 0 (64*W) (scalarProfile W R)
    (fun _ : ℚ => 0) (callback model W values) (scalar model W values)
    (fun _ => le_rfl) (fun _ => le_rfl) (scalar_bound model W values) hW hIndex count hc
  have hw := work model W H values hv hW hIndex
  have hShape : (GeneralPaperNativeSortedRows.one model.rat (fun w => w) W values).2=
      (GeneralPaperNativeRepresentativeSort.run model.rat (fun w => w) W values).2+
      (PaperIndexedArrayConstruction.run (fun w => w) W (callback model W values)).2+16*W := rfl
  have hp := fields_bound W (natBits (cap model W R H))
    [R,(GeneralPaperNativeRepresentativeSort.run model.rat (fun w => w) W values).2,
      (PaperIndexedArrayConstruction.run (fun w => w) W (callback model W values)).2,
      (GeneralPaperNativeRepresentativeSort.run model.rat (fun w => w) W values).2+
      (PaperIndexedArrayConstruction.run (fun w => w) W (callback model W values)).2,
      16*W,(GeneralPaperNativeSortedRows.one model.rat (fun w => w) W values).2] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold cap
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤6*(natBits (cap model W R H)+W)+32*W at hp
  unfold window profile
  dsimp only
  omega

end Blotto.GeneralPaperSortedReferenceConstructionStorage
