import Blotto.GeneralPaperTreeHalfPrice
import Blotto.GeneralPaperOrderedProfitTreeBuild
import Blotto.GeneralPaperIndexedListPrice
import Blotto.GeneralPaperPricedListAppend

/-! Build one zero field, share it through padding, then split each balanced
node by one priced prefix traversal. The root span and input length are
retained caller values. All native trees agree, including empty-list defaults.
Only references to field arrays are copied; no option table is rebuilt. -/
namespace Blotto.GeneralPaperProfitTreeExecution
open GeneralPaperOrderedProfitDP GeneralPaperOrderedProfitTreeBuild
set_option autoImplicit false
set_option maxHeartbeats 6000000

def zeroField {R : Type} [Zero R] (index : ℕ → ℕ) (W K : ℕ) : WeightedField R K × ℕ :=
  let field := PaperIndexedArrayConstruction.run index W (fun _ : Fin K => ((0,(0:R)),64*W))
  ((field.1,0),field.2+64*W)

theorem zeroField_data {R : Type} [Zero R] (index : ℕ → ℕ) (W K : ℕ) :
    (zeroField (R:=R) index W K).1=dummy R K := by
  simp only [zeroField,PaperIndexedArrayConstruction.run_data,dummy]

def pad {R : Type} {K : ℕ} (index primitive : ℕ → ℕ) (W A span m : ℕ)
    (zero : WeightedField R K) (input : List (WeightedField R K)) : List (WeightedField R K) × ℕ :=
  let padding := GeneralPaperIndexedListPrice.run index A (fun _ : Fin (span-m) => (zero,64*W))
  let appended := GeneralPaperPricedListAppend.run W input padding.1
  (appended.1,padding.2+appended.2+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a-b) span m+64*W)

theorem pad_data {R : Type} [LinearOrder R] [AddCommMonoid R] [IsOrderedAddMonoid R] {K : ℕ} (index primitive : ℕ → ℕ) (W A span m height : ℕ)
    (input : List (WeightedField R K)) (hSpan : span=2^height) (hM : m=input.length) :
    (pad index primitive W A span m (dummy R K) input).1=GeneralPaperOrderedProfitTreeBuild.pad height input := by
  simp only [pad,GeneralPaperPricedListAppend.data,GeneralPaperIndexedListPrice.data,hSpan,hM,
    List.ofFn_const,GeneralPaperOrderedProfitTreeBuild.pad]

def build {R : Type} {K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (W : ℕ) (zero : WeightedField R K) :
    (height : ℕ) → ℕ → List (WeightedField R K) → Tree R K height × ℕ
  | 0,_,input => (.leaf (input.headD zero).1,GeneralPaperIntegerWordPrice.compare primitive 0 0+64*W)
  | height+1,span,input =>
    let half := GeneralPaperTreeHalfPrice.run bits primitive W height span
    let parts := GeneralPaperPricedListSplit.run primitive W half.1 input
    let left := build bits primitive W zero height half.1 parts.1.1
    let right := build bits primitive W zero height half.1 parts.1.2
    (.node left.1 right.1,half.2+parts.2+left.2+right.2+
      GeneralPaperPricedListSplit.control primitive W (height+1)+128*W)

theorem build_data {R : Type} [LinearOrder R] [AddCommMonoid R] [IsOrderedAddMonoid R] {K : ℕ} (bits : Bool) (primitive : ℕ → ℕ)
    (W height span : ℕ) (input : List (WeightedField R K)) (hSpan : span=2^height) :
    (build bits primitive W (dummy R K) height span input).1=GeneralPaperOrderedProfitTreeBuild.build height input := by
  induction height generalizing span input with
  | zero => rfl
  | succ height ih =>
    rw [build]
    dsimp only
    rw [GeneralPaperTreeHalfPrice.data bits primitive W height span hSpan,
      GeneralPaperPricedListSplit.data,ih _ _ rfl,ih _ _ rfl]
    rfl

end Blotto.GeneralPaperProfitTreeExecution
