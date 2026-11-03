import Blotto.GeneralPaperCircleSweepBitPrice

/-! Compute one selected shift, then execute the priced ordered sweep on
retained metadata. All initial R*W/2*W products and record references are
priced. The actual selected indices agree with the arithmetic draw. -/
namespace Blotto.GeneralPaperCircleControlDrawBits
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run (model : RationalCostModel) (A R W S l : ℕ) (arcs : List (ℕ×ℕ)) : GeneralPaperCircleSweepBits.State×ℕ :=
  let D := R*W
  let shifted := GeneralPaperNativeShiftExecution.run true model A D S l
  let swept := GeneralPaperCircleSweepBits.run model.rat A R W shifted.1.cell arcs 0 (2*W)
  (swept.1,shifted.2+swept.2+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) R W+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) 2 W+32*A)

theorem data (model : RationalCostModel) (A R W S l : ℕ) (arcs : List (ℕ×ℕ)) :
    (run model A R W S l arcs).1=
      GeneralPaperCircleSweepBits.observe (GeneralPaperNativeCircleControlDraw.run model R W S l arcs).1 := by
  dsimp only [run,GeneralPaperNativeCircleControlDraw.run]
  rw [GeneralPaperNativeShiftExecution.models_data,GeneralPaperCircleSweepBits.data]

def profile (model : RationalCostModel) (A R W S g : ℕ) : ℕ :=
  GeneralPaperNativeShiftPrice.profile true model A (R*W) S+
    (2*R+g+1)*GeneralPaperCircleSweepBitPrice.unitPrice model.rat A R W+
    4*model.rat (GeneralPaperCircleSweepBitBounds.width R W)+32*A

theorem work (model : RationalCostModel) (A R W S l : ℕ) (hR : 0<R) (hW : 0<W) (hS : 0<S) (hl : l<S)
    (arcs : List (ℕ×ℕ)) (hRanges : ∀ arc∈arcs,arc.1+arc.2≤R*W)
    (hOrder : arcs.Pairwise (fun arc other => arc.1≤other.1)) :
    (run model A R W S l arcs).2≤profile model A R W S arcs.length := by
  let shifted := GeneralPaperNativeShiftExecution.run true model A (R*W) S l
  have hd := GeneralPaperNativeShiftPrice.work_bound true model A (R*W) S l (Nat.mul_pos hR hW) hS hl
  have ht := GeneralPaperNativeShiftExecution.cell_bound true model A (R*W) S l (Nat.mul_pos hR hW) hS hl
  have hw := GeneralPaperCircleSweepBitPrice.initial_work model.rat model.monotone A R W shifted.1.cell hR hW ht arcs hRanges hOrder
  let M := GeneralPaperCircleSweepBitBounds.magnitude R W
  have hb := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone
  have h1 := hb (fun a b => a*b) R W M (by dsimp only [M,GeneralPaperCircleSweepBitBounds.magnitude];omega)
    (by dsimp only [M,GeneralPaperCircleSweepBitBounds.magnitude];omega)
    (by dsimp only [M,GeneralPaperCircleSweepBitBounds.magnitude];omega)
  have h2 := hb (fun a b => a*b) 2 W M (by dsimp only [M,GeneralPaperCircleSweepBitBounds.magnitude];omega)
    (by dsimp only [M,GeneralPaperCircleSweepBitBounds.magnitude];omega)
    (by dsimp only [M,GeneralPaperCircleSweepBitBounds.magnitude];omega)
  change shifted.2≤_ at hd
  change _≤2*model.rat (GeneralPaperCircleSweepBitBounds.width R W) at h1 h2
  change shifted.2+(GeneralPaperCircleSweepBits.run model.rat A R W shifted.1.cell arcs 0 (2*W)).2+_+_+32*A≤_
  unfold profile
  omega

end Blotto.GeneralPaperCircleControlDrawBits
