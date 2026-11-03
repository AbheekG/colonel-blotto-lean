import Blotto.GeneralPaperProfitTreePrice
import Blotto.GeneralPaperOrderedRowOptimizer

/-! Assemble the tree from the retained root span and known battlefield
count. One dummy array is shared by all padding references and leaf defaults.
The returned tree is exactly the optimizer's native tree in both models. -/
namespace Blotto.GeneralPaperProfitTreePreparation
open GeneralPaperProfitTreeExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 6000000

def run {R : Type} [Zero R] {K : ℕ} (bits : Bool) (index primitive : ℕ → ℕ)
    (W m height span : ℕ) (input : List (GeneralPaperOrderedProfitTreeBuild.WeightedField R K)) :
    GeneralPaperOrderedProfitDP.Tree R K height × ℕ :=
  let A := if bits then arrayWord W (span+2) else W
  let Z := if bits then arrayWord W K else W
  let zero := zeroField (R:=R) index Z K
  let padded := pad index primitive W A span m zero.1 input
  let tree := build bits primitive W zero.1 height span padded.1
  (tree.1,zero.2+padded.2+tree.2+128*W)

theorem data {R : Type} [LinearOrder R] [AddCommMonoid R] [IsOrderedAddMonoid R] {K : ℕ}
    (bits : Bool) (index primitive : ℕ → ℕ) (W m span : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (input : List (GeneralPaperOrderedProfitTreeBuild.WeightedField R K))
    (hSpan : span=2^prepared.parameters.height) (hM : m=input.length) :
    (run bits index primitive W m prepared.parameters.height span input).1=
      GeneralPaperOrderedRowOptimizer.tree prepared input := by
  unfold run
  dsimp only
  rw [zeroField_data,pad_data index primitive W _ span m prepared.parameters.height input hSpan hM,
    build_data bits primitive W prepared.parameters.height span _ hSpan]
  rfl

theorem zeroField_work {R : Type} [Zero R] (index : ℕ → ℕ) (Z K : ℕ) (hZ : 1≤Z)
    (hIndex : ∀ i≤K,index (binaryWordWidth (i+1))≤Z) :
    (zeroField (R:=R) index Z K).2≤64*K*Z+44*(K+1)*Z+64*Z := by
  have h := GeneralPaperControlArrayPrice.indexed_work index Z (64*Z)
    (fun _ : Fin K => ((0,(0:R)),64*Z)) hZ hIndex (fun _ => Nat.le_refl _)
  change (PaperIndexedArrayConstruction.run index Z (fun _ : Fin K => ((0,(0:R)),64*Z))).2+64*Z≤_
  nlinarith only [h]

theorem pad_work {R : Type} {K : ℕ} (index primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W A span m : ℕ) (zero : GeneralPaperOrderedProfitTreeBuild.WeightedField R K)
    (input : List (GeneralPaperOrderedProfitTreeBuild.WeightedField R K)) (hM : m=input.length) (hFit : m≤span)
    (hBase : index 1≤A) (hIndex : ∀ r<span-m,index (binaryWordWidth (r+1)+1)≤A) :
    (pad index primitive W A span m zero input).2≤
      (span-m)*(64*W+72*A)+18*A+8*W*m+2*W+2*primitive (1+binaryWordWidth span)+64*W := by
  have hl := GeneralPaperIndexedListPrice.work index A (64*W) (fun _ : Fin (span-m) => (zero,64*W))
    hBase hIndex (fun _ => Nat.le_refl _)
  have ha := GeneralPaperPricedListAppend.work W input
    (GeneralPaperIndexedListPrice.run index A (fun _ : Fin (span-m) => (zero,64*W))).1
  have hs := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a-b) span m span
    (Nat.le_refl _) hFit (Nat.sub_le _ _)
  change (GeneralPaperIndexedListPrice.run index A (fun _ : Fin (span-m) => (zero,64*W))).2+
    (GeneralPaperPricedListAppend.run W input (GeneralPaperIndexedListPrice.run index A (fun _ : Fin (span-m) => (zero,64*W))).1).2+_+64*W≤_
  rw [ha,←hM]
  omega

def bitProfile (primitive : ℕ → ℕ) (W m K height span : ℕ) : ℕ :=
  let A := arrayWord W (span+2)
  let Z := arrayWord W K
  (64*K*Z+44*(K+1)*Z+64*Z)+
    ((span-m)*(64*W+72*A)+18*A+8*W*m+2*W+2*primitive (1+binaryWordWidth span)+64*W)+
    1024*2^height*(height+1)*(W+primitive (GeneralPaperTreeHalfPrice.width height))+128*W

theorem bit_work {R : Type} [Zero R] {K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W m height span : ℕ) (input : List (GeneralPaperOrderedProfitTreeBuild.WeightedField R K))
    (hSpan : span=2^height) (hM : m=input.length) (hFit : m≤span) :
    (run true (fun x => x) primitive W m height span input).2≤bitProfile primitive W m K height span := by
  let A := arrayWord W (span+2)
  let Z := arrayWord W K
  let zero := zeroField (R:=R) (fun x => x) Z K
  let padded := pad (fun x => x) primitive W A span m zero.1 input
  have hz := zeroField_work (R:=R) (fun x => x) Z K (GeneralPaperSummaryArrayControls.array_word_positive W K)
    (fun i hi => GeneralPaperSummaryArrayControls.array_index W K i hi)
  have hp := pad_work (fun x => x) primitive hMono W A span m zero.1 input hM hFit
    (GeneralPaperSummaryArrayControls.array_word_positive W (span+2)) (by
      intro r hr
      have hw := binaryWordWidth_mono (show r+1≤(span+2)+1 by omega)
      dsimp only [A]
      unfold arrayWord
      omega)
  have ht := GeneralPaperProfitTreePrice.build_bit_work primitive hMono W height height span zero.1 padded.1 (Nat.le_refl _) hSpan
  change zero.2+padded.2+(build true primitive W zero.1 height span padded.1).2+128*W≤_
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hz hp) ht) _

def arithmeticProfile (m K height span : ℕ) : ℕ :=
  (64*K+44*(K+1)+64)+((span-m)*136+18+8*m+2+2+64)+1024*2^height*(height+1)^2+128

theorem arithmetic_work {R : Type} [Zero R] {K : ℕ} (m height span : ℕ)
    (input : List (GeneralPaperOrderedProfitTreeBuild.WeightedField R K))
    (hSpan : span=2^height) (hM : m=input.length) (hFit : m≤span) :
    (run false (fun _ => 1) (fun _ => 1) 1 m height span input).2≤arithmeticProfile m K height span := by
  let zero := zeroField (R:=R) (fun _ => 1) 1 K
  let padded := pad (fun _ => 1) (fun _ => 1) 1 1 span m zero.1 input
  have hz := zeroField_work (R:=R) (fun _ => 1) 1 K (Nat.le_refl _) (fun _ _ => Nat.le_refl _)
  have hp := pad_work (fun _ => 1) (fun _ => 1) (fun _ _ _ => Nat.le_refl _) 1 1 span m zero.1 input hM hFit
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _)
  have ht := GeneralPaperProfitTreePrice.build_arithmetic_work height span zero.1 padded.1 hSpan
  change zero.2+padded.2+(build false (fun _ => 1) 1 zero.1 height span padded.1).2+128≤_
  simpa only [arithmeticProfile,Nat.mul_one] using
    Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hz hp) ht) 128

end Blotto.GeneralPaperProfitTreePreparation
