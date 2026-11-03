import Blotto.GeneralPaperNamedCircleLaw

/-! The complete arithmetic draw reuses prepared data and costs
O(n+R+word(RW)). No operand-height observer runs on its data path. Bit
prices for the final rational products remain operand-sensitive, while a
complete priced bit-control sweep is a separate obligation. -/
namespace Blotto.GeneralPaperNamedCirclePrice
open GeneralPaperNamedCircleExecution GeneralPaperLightFieldIndexEquiv
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem light_arithmetic_work {g R : ℕ} (hR : 0<R) (coefficients : FixedArrayTable g ℚ)
    (sorted : FixedArrayTable R ℚ) (chosen : FixedArrayTable g ℕ) :
    (GeneralPaperNativeLightBids.run (fun _ => 1) (fun _ => 1) 1 hR coefficients sorted chosen).2≤126*g+44 := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 82
    (fun j => GeneralPaperNativeLightBids.coordinate (fun _ => 1) (fun _ => 1) 1 hR sorted (coefficients.read j) (chosen.read j))
    (by decide) (fun _ _ => le_rfl) (by
      intro j
      simp only [GeneralPaperNativeLightBids.coordinate,GeneralPaperRationalPrimitivePrice.binary]
      decide)
  change (PaperIndexedArrayConstruction.run (fun _ => 1) 1 _).2≤_
  nlinarith only [h]

theorem assemble_arithmetic_work {n R : ℕ} (state : GeneralPaperLightFieldScan.State n)
    (hR : 0<R) (c : ℚ) (prepared : Prepared state R) (chosen : FixedArrayTable state.light.size ℕ)
    (hBijective : Function.Bijective (mapping state)) :
    (assemble (fun _ => 1) (fun _ => 1) 1 state hR c prepared chosen).2≤700*(n+1) := by
  let light := GeneralPaperNativeLightBids.run (fun _ => 1) (fun _ => 1) 1 hR prepared.coefficients prepared.sorted chosen
  let named := GeneralPaperOriginalFieldScatter.run (fun _ => 1) 1 state prepared.kept light.1
  have hl := light_arithmetic_work hR prepared.coefficients prepared.sorted chosen
  have hn := GeneralPaperOriginalScatterModels.arithmetic_work state prepared.kept light.1 hBijective
  have hc := GeneralPaperRationalOutputScale.arithmetic_work c named.1
  have hs := GeneralPaperOriginalScatterLaw.size state hBijective
  change light.2≤126*state.light.size+44 at hl
  change named.2≤451*(n+1) at hn
  change light.2+named.2+(GeneralPaperRationalOutputScale.run (fun _ => 1) (fun _ => 1) 1 c named.1).2+32*1≤_
  nlinarith only [hl,hn,hc,hs]

theorem draw_arithmetic_work {n R : ℕ} (model : RationalCostModel) (W S : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (hR : 0<R) (hW : 0<W) (hS : 0<S) (c : ℚ) (kept : FixedArrayTable state.heavy.size ℚ)
    (row : FixedArrayTable R ℚ) (weights : FixedArrayTable state.light.size ℕ)
    (hs : ∑ j,weights.read j=W) (hBijective : Function.Bijective (mapping state)) (l : Fin S) :
    (drawArithmetic model W S state hR c
      (prepare (fun _ => 1) (fun _ => 1) 1 W state kept row weights).1 l).2≤
        1024*(binaryWordWidth (R*W)+1)+24*R+816*(n+1) := by
  have hChoice := GeneralPaperNativeChoiceArray.arithmetic_work model (fun _ => 1) 1 R W S l.val
    hR hW hS l.isLt weights hs
  have hOutput := assemble_arithmetic_work state hR c
    (prepare (fun _ => 1) (fun _ => 1) 1 W state kept row weights).1
    (GeneralPaperNativeChoiceArray.draw model R W S l.val
      (GeneralPaperNativeChoiceArray.prepare (fun _ => 1) 1 R weights).1).1 hBijective
  have hSize := GeneralPaperOriginalScatterLaw.size state hBijective
  change (GeneralPaperNativeChoiceArray.draw model R W S l.val
    (GeneralPaperNativeChoiceArray.prepare (fun _ => 1) 1 R weights).1).2+_+16≤_
  dsimp only [prepare] at hOutput ⊢
  nlinarith only [hChoice,hOutput,hSize]

end Blotto.GeneralPaperNamedCirclePrice
