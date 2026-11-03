import Blotto.GeneralPaperRankExecutionData

/-! Rank indices, binary-search counters, native annotations and code
comparands have a derived common word. V bounds the code values; callers
later derive it from actual summary/cut arrays. The envelope is analytical.
-/
namespace Blotto.GeneralPaperRankOperands
open GeneralPaperRankExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def magnitude (n depth V : ℕ) : ℕ := 4*n+64*(depth+1)^2+V+256
def width (depth V : ℕ) : ℕ := 256+32*(depth+binaryWordWidth (V+1))

theorem word_bound (n depth V : ℕ) (hSize : n<2^depth) :
    1+binaryWordWidth (magnitude n depth V)≤width depth V := by
  have hn := (binaryWordWidth_mono hSize.le).trans (GeneralPaperNatPowerOperands.power_width 2 depth)
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2] at hn
  have h4n := binaryWordWidth_mul 4 n
  have hd := GeneralPaperInitializerControlCounters.word_le_self (depth+1)
  have hs := binaryWordWidth_mul (depth+1) (depth+1)
  rw [←pow_two] at hs
  have hm := binaryWordWidth_mul 64 ((depth+1)^2)
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (4*n) (64*(depth+1)^2)
  have hb := GeneralPaperRayOperandWidthEnvelope.word_add (4*n+64*(depth+1)^2) V
  have hc := GeneralPaperRayOperandWidthEnvelope.word_add (4*n+64*(depth+1)^2+V) 256
  have hv := binaryWordWidth_mono (show V≤V+1 by omega)
  have h4 : binaryWordWidth 4=3 := by decide
  have h64 : binaryWordWidth 64=7 := by decide
  have h256 : binaryWordWidth 256=9 := by decide
  unfold magnitude width
  omega

theorem basic (n depth V : ℕ) :
    n≤magnitude n depth V ∧ V≤magnitude n depth V ∧ depth+1≤magnitude n depth V ∧
      256≤magnitude n depth V ∧ 64*(depth+1)^2≤magnitude n depth V := by
  unfold magnitude
  refine ⟨by omega,by omega,?_,by omega,by omega⟩
  nlinarith only [Nat.zero_le depth]

theorem midpoint_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W n depth V lo hi : ℕ)
    (hOrder : lo≤hi) (hHi : hi≤n) (hSize : n<2^depth) :
    (GeneralPaperRankMidpointPrice.run true primitive W depth lo hi).2≤8*primitive (width depth V)+64*W := by
  let N := magnitude n depth V
  let L := width depth V
  have hN := basic n depth V
  have hMeta : 12*depth+2≤64*(depth+1)^2 := by nlinarith only [Nat.zero_le depth]
  have hWord := word_bound n depth V hSize
  have price (op : ℕ → ℕ → ℕ) (a b : ℕ) (ha : a≤N) (hb : b≤N) (hc : op a b≤N) :
      GeneralPaperNaturalPrimitivePrice.binary primitive op a b≤2*primitive L :=
    (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono op a b N ha hb hc).trans
      (Nat.mul_le_mul_left 2 (hMono hWord))
  have hCore : 4*n≤N := by dsimp [N,magnitude]; omega
  have a := price (fun a b => a+b) lo hi (by dsimp only [N]; omega) (by dsimp only [N]; omega) (by omega)
  have b := price (fun a b => a/b) (lo+hi) 2 (by omega) (by dsimp only [N]; omega)
    ((Nat.div_le_self (lo+hi) 2).trans (by omega))
  have c := price (fun a b => a*b) 12 depth (by dsimp only [N]; omega) (by dsimp only [N]; omega)
    (by dsimp only [N]; omega)
  have d := price (fun a b => a+b) (12*depth) 2 (by dsimp only [N]; omega) (by dsimp only [N]; omega)
    (by dsimp only [N]; omega)
  change _≤8*primitive L+64*W
  unfold GeneralPaperRankMidpointPrice.run
  simp only [ite_true]
  omega

theorem control_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W n depth V fuel lo hi : ℕ)
    (hFuel : fuel+1≤depth) (hOrder : lo≤hi) (hHi : hi≤n) (hSize : n<2^depth) :
    control primitive W fuel lo hi≤4*primitive (width depth V)+64*W := by
  let N := magnitude n depth V
  let L := width depth V
  have hN := basic n depth V
  have hWord := word_bound n depth V hSize
  have w (a : ℕ) (ha : a≤N) : 1+binaryWordWidth a≤L :=
    (Nat.add_le_add_left (binaryWordWidth_mono ha) 1).trans hWord
  have ht := GeneralPaperIntegerWordPrice.compare_le primitive hMono (fuel+1) 0 L
    (w _ (by dsimp only [N]; omega)) (w _ (by omega))
  have hd := (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a-b) (fuel+1) 1 N
    (by dsimp only [N]; omega) (by dsimp only [N]; omega) (by dsimp only [N]; omega)).trans
      (Nat.mul_le_mul_left 2 (hMono hWord))
  have ho := GeneralPaperIntegerWordPrice.compare_le primitive hMono lo hi L
    (w _ (by dsimp only [N]; omega)) (w _ (by dsimp only [N]; omega))
  change _≤2*primitive L at hd
  unfold GeneralPaperRankExecution.control
  change _≤4*primitive L+64*W
  omega

theorem finish_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W n depth V fuel : ℕ)
    (child : GeneralPaperRankSearch.Result) (mid : GeneralPaperRankMidpointPrice.Result)
    (hFuel : fuel≤depth) (hSize : n<2^depth)
    (hChild : child.work≤fuel*(12*depth+34)+8) (hProbes : child.probes≤fuel) (hMid : mid.work=12*depth+2) :
    (finish primitive W child mid).2≤6*primitive (width depth V)+96*W := by
  let N := magnitude n depth V
  let L := width depth V
  have hN := basic n depth V
  have hWord := word_bound n depth V hSize
  have hMul := Nat.mul_le_mul_right (12*depth+34) hFuel
  have hMeta : child.work+mid.work+32≤64*(depth+1)^2 := by nlinarith only [hChild,hMul,hMid,Nat.zero_le depth]
  have hVisits : child.probes+1≤N := by dsimp only [N]; omega
  have price (a b : ℕ) (ha : a≤N) (hb : b≤N) (hc : a+b≤N) :
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) a b≤2*primitive L :=
    (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a+b) a b N ha hb hc).trans
      (Nat.mul_le_mul_left 2 (hMono hWord))
  have a := price child.work mid.work (by dsimp only [N]; omega) (by dsimp only [N]; omega) (by dsimp only [N]; omega)
  have b := price (child.work+mid.work) 32 (by dsimp only [N]; omega) (by dsimp only [N]; omega) (by dsimp only [N]; omega)
  have c := price child.probes 1 (by omega) (by omega) hVisits
  change _≤6*primitive L+96*W
  unfold finish
  dsimp only
  omega

end Blotto.GeneralPaperRankOperands
