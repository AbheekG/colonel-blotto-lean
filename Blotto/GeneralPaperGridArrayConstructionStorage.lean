import Blotto.GeneralPaperProfitOrderConstructionStorage

/-! Native ordered-list packing and scaled-array fill prefixes. Both
buffers reserve the complete native grid capacity. A reached packing state
inherits its value cap by preservation, without reconstructing a prefix or
executing a validation/encoding pass. -/
namespace Blotto.GeneralPaperGridArrayConstructionStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def Good (U : ℕ) (s : List ℕ × Array ℕ) : Prop := (∀ x∈s.1,x≤U) ∧ ∀ x∈s.2,x≤U

theorem next_good (U : ℕ) (s : List ℕ × Array ℕ) (hs : Good U s) : Good U (ReferenceArrayBuilder.next s) := by
  rcases s with ⟨xs,data⟩
  cases xs with
  | nil => exact hs
  | cons x rest =>
    refine ⟨fun y hy => hs.1 y (List.mem_cons_of_mem _ hy),?_⟩
    intro y hy
    rcases Array.mem_push.mp hy with hy|hy
    · exact hs.2 y hy
    · rw [hy]; exact hs.1 x (List.mem_cons_self ..)

theorem prefix_good (U used : ℕ) (xs : List ℕ) (hx : ∀ x∈xs,x≤U) :
    Good U (ReferenceArrayBuilder.advance used (xs,#[])) := by
  induction used with
  | zero =>
    refine ⟨hx,?_⟩
    intro x hx
    obtain ⟨i,hi,_⟩ := Array.mem_iff_getElem.mp hx
    have hZero : i<0 := hi
    omega
  | succ used ih => exact next_good U _ ih

def packing (W copied : ℕ) (xs : List ℕ) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W xs.length natBits (ReferenceArrayBuilder.advance copied (xs,#[])).2

theorem packing_bound (W U copied : ℕ) (xs : List ℕ) (hx : ∀ x∈xs,x≤U) :
    packing W copied xs≤xs.length*(natBits U+W)+64*W := by
  apply GeneralPaperEncodedReferenceVector.reserved_bound W (natBits U) xs.length natBits _
    (ReferenceArrayBuilder.every_prefix_table_size copied xs)
  intro i
  exact Nat.add_le_add_left (binaryWordWidth_mono ((prefix_good U copied xs hx).2 _ (Array.getElem_mem i.isLt))) 1

def frames (W n : ℕ) : ℕ := (n+1)*(4*natBits (n+1)+128*W)

def packingWindow (W copied : ℕ) (xs : List ℕ) : ℕ :=
  listFootprint W natBits xs+2*packing W copied xs+frames W xs.length+128*W

theorem packing_window (W U copied : ℕ) (xs : List ℕ) (hx : ∀ x∈xs,x≤U) :
    packingWindow W copied xs≤xs.length*(natBits U+2*W)+32*W+
      2*(xs.length*(natBits U+W)+64*W)+frames W xs.length+128*W :=
  Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add (list_bound W (natBits U) natBits xs
    (fun x hx' => Nat.add_le_add_left (binaryWordWidth_mono (hx x hx')) 1))
    (Nat.mul_le_mul_left 2 (packing_bound W U copied xs hx))) _) _

def scaledPrefix {n : ℕ} (index primitive : ℕ → ℕ) (W q : ℕ) (values : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W n natBits
    (PaperIndexedArrayConstruction.fill index W (fun r : Fin n =>
      (q*values.read r,GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) q (values.read r)+16*W)) count hc).1

theorem scaled_bound {n : ℕ} (index primitive : ℕ → ℕ) (W q w B : ℕ) (values : FixedArrayTable n ℕ)
    (hv : ∀ i,values.read i≤2*GeneralPaperProfitGridPoints.denominator w B)
    (count : ℕ) (hc : count≤n) :
    scaledPrefix index primitive W q values count hc≤n*(GeneralPaperEncodedProfitGrid.word q w B+W)+64*W := by
  have hWord (r : Fin n) : natBits (q*values.read r)≤GeneralPaperEncodedProfitGrid.word q w B := by
    have hn := binaryWordWidth_mono (hv r)
    have hp := GeneralPaperNatPowerOperands.power_width 2 B
    have hd := binaryWordWidth_mul (2^B) w
    have he := binaryWordWidth_mul 2 (GeneralPaperProfitGridPoints.denominator w B)
    have hm := binaryWordWidth_mul q (values.read r)
    have hw := binaryWordWidth_mono (Nat.le_add_right w 1)
    have h2 : binaryWordWidth 2=2 := by decide
    change binaryWordWidth (GeneralPaperProfitGridPoints.denominator w B)≤_ at hd
    rw [h2] at hp he
    unfold natBits GeneralPaperEncodedProfitGrid.word
    omega
  exact GeneralPaperEncodedReferenceVector.indexed_reserved_prefix index W W _ natBits
    (fun r : Fin n => (q*values.read r,GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) q (values.read r)+16*W)) hWord count hc

theorem native_scaled (index primitive : ℕ → ℕ) (W q w B count : ℕ)
    (hc : count≤(GeneralPaperProfitGridPrepare.prepare q w B).size) :
    scaledPrefix index primitive W q (GeneralPaperProfitGridPrepare.prepare q w B).numerators count hc≤
      ((B+1)*w+2)*(GeneralPaperEncodedProfitGrid.word q w B+W)+64*W :=
  (scaled_bound index primitive W q w B _ (GeneralPaperProfitGridPrepare.numerator_bound q w B) count hc).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (GeneralPaperProfitGridPrepare.size_bound q w B)) _)

end Blotto.GeneralPaperGridArrayConstructionStorage
