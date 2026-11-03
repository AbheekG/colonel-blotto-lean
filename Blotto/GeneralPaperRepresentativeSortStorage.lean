import Blotto.GeneralPaperFinRangeStorage
import Blotto.GeneralPaperSelectedSortStorage
import Blotto.GeneralPaperListReferenceConstructionStorage
import Blotto.GeneralPaperSourceQuantizedAnchorReachedRates

/-! Literal representative-reference sorting, with its selected native
fuel, full source values, original and sorted reference lists, returned
order array, comparator operands and list-materialization frames. All
observers are erased; original row indices still break rational ties. -/
namespace Blotto.GeneralPaperRepresentativeSortStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (arrayFootprint arrayProfile array_bound)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def comparisonPrice (model : RationalCostModel) (W R : ℕ) : ℕ := 2*model.rat R+80*W
def price (model : RationalCostModel) (W T R : ℕ) : ℕ :=
  GeneralPaperNativeRepresentativeSort.profile T W (model.rat R)
def compareCap (W T C : ℕ) : ℕ := T+C+80*W+1

def scalarWindow {T : ℕ} (model : RationalCostModel) (W : ℕ)
    (values : FixedArrayTable T ℚ) (a b : Fin T) : ℕ :=
  let x := values.read a
  let y := values.read b
  let p := model.rat (RationalExpression.pairWidth x y)
  let u := binaryWordWidth (a.val+1)
  let v := binaryWordWidth (b.val+1)
  rationalWordWidth x+rationalWordWidth y+2*p+8*u+8*v+
    fields W [a.val,b.val,u,v,if x<y then 1 else 0,if x=y then 1 else 0,
      if a≤b then 1 else 0,if (GeneralPaperNativeRepresentativeSort.compare model.rat (fun w => w) W values a b).1 then 1 else 0,
      (GeneralPaperNativeRepresentativeSort.compare model.rat (fun w => w) W values a b).2,p,2*p,2*p+8*u,2*p+8*u+8*v]+128*W

def scalarProfile (W T R C : ℕ) : ℕ :=
  2*R+C+13*(natBits (compareCap W T C)+W)+160*W

theorem compare_work {T : ℕ} (model : RationalCostModel) (W R : ℕ)
    (values : FixedArrayTable T ℚ) (hValues : ∀ i,rationalWordWidth (values.read i)≤R)
    (hIndex : binaryWordWidth (T+1)≤W) (a b : Fin T) :
    (GeneralPaperNativeRepresentativeSort.compare model.rat (fun w => w) W values a b).2≤comparisonPrice model W R :=
  GeneralPaperNativeRepresentativeSort.compare_work model.rat (fun w => w) model.monotone W R values hValues
    (fun _i hi => (binaryWordWidth_mono (Nat.add_le_add_right hi 1)).trans hIndex) a b

theorem scalar_bound {T : ℕ} (model : RationalCostModel) (W R : ℕ)
    (values : FixedArrayTable T ℚ) (hValues : ∀ i,rationalWordWidth (values.read i)≤R)
    (hIndex : binaryWordWidth (T+1)≤W) (a b : Fin T) :
    scalarWindow model W values a b≤scalarProfile W T R (comparisonPrice model W R) := by
  let x := values.read a
  let y := values.read b
  let p := model.rat (RationalExpression.pairWidth x y)
  let u := binaryWordWidth (a.val+1)
  let v := binaryWordWidth (b.val+1)
  let c := (GeneralPaperNativeRepresentativeSort.compare model.rat (fun w => w) W values a b)
  have hp : p≤model.rat R := model.monotone (max_le (hValues a) (hValues b))
  have hu : u≤W := (binaryWordWidth_mono (Nat.add_le_add_right a.isLt.le 1)).trans hIndex
  have hv : v≤W := (binaryWordWidth_mono (Nat.add_le_add_right b.isLt.le 1)).trans hIndex
  have hc := compare_work model W R values hValues hIndex a b
  change c.2≤comparisonPrice model W R at hc
  have hs : c.2=2*p+8*u+8*v+64*W := rfl
  have hf := fields_bound W (natBits (compareCap W T (comparisonPrice model W R)))
    [a.val,b.val,u,v,if x<y then 1 else 0,if x=y then 1 else 0,
      if a≤b then 1 else 0,if c.1 then 1 else 0,c.2,p,2*p,2*p+8*u,2*p+8*u+8*v] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold compareCap comparisonPrice at *
      all_goals first | split_ifs <;> omega | omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤13*(natBits (compareCap W T (comparisonPrice model W R))+W)+32*W at hf
  have hx := hValues a
  have hy := hValues b
  change rationalWordWidth x≤R at hx
  change rationalWordWidth y≤R at hy
  change rationalWordWidth x+rationalWordWidth y+2*p+8*u+8*v+
    GeneralPaperEncodedScalarStorage.fields W [a.val,b.val,u,v,if x<y then 1 else 0,if x=y then 1 else 0,
      if a≤b then 1 else 0,if c.1 then 1 else 0,c.2,p,2*p,2*p+8*u,2*p+8*u+8*v]+128*W≤_
  unfold scalarProfile
  omega

def metadataCap (model : RationalCostModel) (W T R : ℕ) : ℕ :=
  T+price model W T R+(16*T+16)*W+1

def window {T : ℕ} (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable T ℚ)
    (used copied : ℕ) (active : Option (Fin T×Fin T)) : ℕ :=
  let compare := GeneralPaperNativeRepresentativeSort.compare model.rat (fun w => w) W values
  let sorted := GeneralPaperPricedSort.run compare W (List.finRange T)
  let stored := PaperListReferenceArray.run (fun w => w) W sorted.1
  let result := GeneralPaperNativeRepresentativeSort.run model.rat (fun w => w) W values
  let encode := fun i : Fin T => natBits i.val
  arrayFootprint W rationalWordWidth values+
    listFootprint W encode (List.finRange T)+listFootprint W encode sorted.1+
    arrayFootprint W encode result.1+
    GeneralPaperSelectedSortStorage.window model W encode compare (List.finRange T)+
    GeneralPaperListReferenceConstructionStorage.window W used encode sorted.1+
    (match active with | none => 64*W | some (a,b) => scalarWindow model W values a b)+
    GeneralPaperFinRangeStorage.window W T copied+fields W [T,sorted.2,stored.2,result.2,(16*T+16)*W,sorted.2+stored.2]+128*W

def profile (model : RationalCostModel) (W T R : ℕ) : ℕ :=
  let P := natBits T
  let C := comparisonPrice model W R
  arrayProfile W T R+2*(T*(P+2*W)+32*W)+arrayProfile W T P+
    GeneralPaperSelectedSortStorage.profile model W P C T+
    GeneralPaperListReferenceConstructionStorage.profile W P T+
    scalarProfile W T R C+64*W+GeneralPaperFinRangeStorage.profile W T+6*(natBits (metadataCap model W T R)+W)+160*W

theorem work {T : ℕ} (model : RationalCostModel) (W R : ℕ)
    (values : FixedArrayTable T ℚ) (hValues : ∀ i,rationalWordWidth (values.read i)≤R)
    (hW : 1≤W) (hIndex : binaryWordWidth (T+1)≤W) :
    (GeneralPaperNativeRepresentativeSort.run model.rat (fun w => w) W values).2≤price model W T R :=
  GeneralPaperNativeRepresentativeSort.work model.rat (fun w => w) model.monotone W R hW values hValues
    (fun _i hi => (binaryWordWidth_mono (Nat.add_le_add_right hi 1)).trans hIndex)

theorem bounded {T : ℕ} (model : RationalCostModel) (W R : ℕ)
    (values : FixedArrayTable T ℚ) (hValues : ∀ i,rationalWordWidth (values.read i)≤R)
    (hW : 1≤W) (hIndex : binaryWordWidth (T+1)≤W) (used copied : ℕ) (active : Option (Fin T×Fin T)) :
    window model W values used copied active≤profile model W T R := by
  let compare := GeneralPaperNativeRepresentativeSort.compare model.rat (fun w => w) W values
  let sorted := GeneralPaperPricedSort.run compare W (List.finRange T)
  let stored := PaperListReferenceArray.run (fun w => w) W sorted.1
  let result := GeneralPaperNativeRepresentativeSort.run model.rat (fun w => w) W values
  let encode := fun i : Fin T => natBits i.val
  have he (i : Fin T) : encode i≤natBits T := Nat.add_le_add_left (binaryWordWidth_mono i.isLt.le) 1
  have hl : sorted.1.length=T := by dsimp only [sorted]; rw [GeneralPaperPricedSort.length,List.length_finRange]
  have hValues' := array_bound W R rationalWordWidth values hValues
  have hInput := list_bound W (natBits T) encode (List.finRange T) (fun i _ => he i)
  rw [List.length_finRange] at hInput
  have hSorted := list_bound W (natBits T) encode sorted.1 (fun i _ => he i)
  rw [hl] at hSorted
  have hOutput := array_bound W (natBits T) encode result.1 (fun i => he (result.1.read i))
  have hSort := GeneralPaperSelectedSortStorage.bounded model W (natBits T) (comparisonPrice model W R) T
    encode compare (List.finRange T) (by simp) (fun i _ => he i)
    (fun a _ b _ => compare_work model W R values hValues hIndex a b)
  have hStore := GeneralPaperListReferenceConstructionStorage.bounded W (natBits T) T used encode sorted.1
    hl.le (fun i _ => he i) hW hIndex
  have hActive : (match active with | none => 64*W | some (a,b) => scalarWindow model W values a b)≤
      scalarProfile W T R (comparisonPrice model W R)+64*W := by
    cases active with
    | none => exact Nat.le_add_left _ _
    | some ab => exact (scalar_bound model W R values hValues hIndex ab.1 ab.2).trans (Nat.le_add_right _ _)
  have hRange := GeneralPaperFinRangeStorage.bounded W T copied
  have hw := work model W R values hValues hW hIndex
  change result.2≤price model W T R at hw
  have hShape : result.2=sorted.2+stored.2+(16*T+16)*W := rfl
  have hf := fields_bound W (natBits (metadataCap model W T R))
    [T,sorted.2,stored.2,result.2,(16*T+16)*W,sorted.2+stored.2] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤6*(natBits (metadataCap model W T R)+W)+32*W at hf
  change arrayFootprint W rationalWordWidth values+listFootprint W encode (List.finRange T)+
    listFootprint W encode sorted.1+arrayFootprint W encode result.1+
    GeneralPaperSelectedSortStorage.window model W encode compare (List.finRange T)+
    GeneralPaperListReferenceConstructionStorage.window W used encode sorted.1+_+
    GeneralPaperFinRangeStorage.window W T copied+GeneralPaperEncodedScalarStorage.fields W [T,sorted.2,stored.2,result.2,(16*T+16)*W,sorted.2+stored.2]+128*W≤_
  unfold profile
  dsimp only
  omega

end Blotto.GeneralPaperRepresentativeSortStorage
