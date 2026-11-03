import Blotto.GeneralPaperCircleControlDrawBits

/-! Materialize actual bit-priced sweep indices once in a sized reference
array. Metadata is retained from preparation; no sorting/building is rerun. -/
namespace Blotto.GeneralPaperNativeChoiceArrayBits
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem length {g : ℕ} (model : RationalCostModel) (A R W S l : ℕ) (prepared : GeneralPaperNativeChoiceArray.Prepared g) :
    (GeneralPaperCircleControlDrawBits.run model A R W S l prepared.arcs).1.indices.length=g := by
  rw [GeneralPaperCircleControlDrawBits.data]
  exact GeneralPaperNativeChoiceArray.draw_length model R W S l prepared

def run {g : ℕ} (model : RationalCostModel) (index : ℕ → ℕ) (A R W S l : ℕ)
    (prepared : GeneralPaperNativeChoiceArray.Prepared g) : FixedArrayTable g ℕ×ℕ :=
  let chosen := GeneralPaperCircleControlDrawBits.run model A R W S l prepared.arcs
  let stored := PaperListReferenceArray.run index A chosen.1.indices
  (⟨stored.1,by rw [PaperListReferenceArray.size,length]⟩,chosen.2+stored.2+32*A)

theorem data {g : ℕ} (model : RationalCostModel) (index : ℕ → ℕ) (A R W S l : ℕ)
    (prepared : GeneralPaperNativeChoiceArray.Prepared g) :
    (run model index A R W S l prepared).1=(GeneralPaperNativeChoiceArray.draw model R W S l prepared).1 := by
  unfold run GeneralPaperNativeChoiceArray.draw
  dsimp only
  congr 1
  rw [PaperListReferenceArray.data,PaperListReferenceArray.data,GeneralPaperCircleControlDrawBits.data]
  rfl

def profile (model : RationalCostModel) (A R W S g : ℕ) : ℕ :=
  GeneralPaperCircleControlDrawBits.profile model A R W S g+64*(g+1)*A+32*A

theorem work {g : ℕ} (model : RationalCostModel) (A R W S l : ℕ) (hR : 0<R) (hW : 0<W) (hS : 0<S) (hl : l<S)
    (price : ℕ → ℕ) (Ap : ℕ) (weights : FixedArrayTable g ℕ) (hs : ∑ j,weights.read j=W)
    (hA : 1≤A) (hIndex : binaryWordWidth (g+1)≤A) :
    (run model (fun w => w) A R W S l (GeneralPaperNativeChoiceArray.prepare price Ap R weights).1).2≤
      profile model A R W S g := by
  have hSum : (List.ofFn weights.read).sum=W := by rw [List.sum_ofFn];exact hs
  have hRanges : ∀ arc∈(GeneralPaperNativeChoiceArray.prepare price Ap R weights).1.arcs,arc.1+arc.2≤R*W := by
    intro arc hm
    have hh := GeneralPaperCircleArcMetadata.ranges price Ap R (List.ofFn weights.read) 0 arc hm
    simpa only [GeneralPaperCircleArcMetadata.total,hSum,Nat.zero_add] using hh
  have hOrder := GeneralPaperCircleArcMetadata.ordered price Ap R (List.ofFn weights.read) 0
  have hc := GeneralPaperCircleControlDrawBits.work model A R W S l hR hW hS hl
    (GeneralPaperNativeChoiceArray.prepare price Ap R weights).1.arcs hRanges hOrder
  rw [(GeneralPaperNativeChoiceArray.prepare price Ap R weights).1.count] at hc
  have ht := PaperListReferenceArray.bit_work A
    (GeneralPaperCircleControlDrawBits.run model A R W S l (GeneralPaperNativeChoiceArray.prepare price Ap R weights).1.arcs).1.indices hA
    (by rw [length];exact hIndex)
  rw [length] at ht
  dsimp only [run]
  unfold profile
  omega

end Blotto.GeneralPaperNativeChoiceArrayBits
