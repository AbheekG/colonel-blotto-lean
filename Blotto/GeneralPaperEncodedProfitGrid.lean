import Blotto.GeneralPaperEncodedPreparedPowers

/-! Both retained profit-grid arrays and every scalar control/annotation.
The generic local word is proved from native grid construction and then
bounded by the source's logarithmic operand envelope. -/
namespace Blotto.GeneralPaperEncodedProfitGrid
open GeneralPaperEncodedScalarStorage GeneralPaperProfitGridPrepare GeneralPaperProfitGridPoints
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def word (q w B : ℕ) : ℕ := 4096*(1+binaryWordWidth q+B+binaryWordWidth (w+1))

theorem words (q w B : ℕ) :
    let g := prepare q w B
    (∀ i,natBits (g.numerators.read i)≤word q w B) ∧
    (∀ i,natBits (g.leafNumerators.read i)≤word q w B) ∧
    (∀ x∈[g.size,g.depth,g.profitDenominator,g.scaledWork,g.depthWork],natBits x≤word q w B) := by
  let g := prepare q w B
  let J := (B+1)*w+2
  have hs : g.size≤J := size_bound q w B
  have hw := binaryWordWidth_mono (show w≤w+1 by omega)
  have hp := GeneralPaperNatPowerOperands.power_width 2 B
  have hd := binaryWordWidth_mul (2^B) w
  have hu := binaryWordWidth_mul 2 (denominator w B)
  have h2 : binaryWordWidth 2=2 := by decide
  change binaryWordWidth (denominator w B)≤_ at hd
  rw [h2] at hp hu
  have hden : natBits g.profitDenominator≤word q w B := by
    change 1+binaryWordWidth (denominator w B)≤_
    unfold word
    omega
  have hnums : ∀ i,natBits (g.numerators.read i)≤word q w B := by
    intro i
    have hn := binaryWordWidth_mono (numerator_bound q w B i)
    change binaryWordWidth (g.numerators.read i)≤binaryWordWidth (2*denominator w B) at hn
    unfold natBits word
    omega
  have hleaf : ∀ i,natBits (g.leafNumerators.read i)≤word q w B := by
    intro i
    have hn := binaryWordWidth_mono (numerator_bound q w B i)
    change binaryWordWidth (g.numerators.read i)≤binaryWordWidth (2*denominator w B) at hn
    have hm := binaryWordWidth_mul q (g.numerators.read i)
    rw [show g.leafNumerators.read i=q*g.numerators.read i from scaled_read q w B i]
    unfold natBits word
    omega
  have hb := GeneralPaperInitializerControlCounters.word_le_self (B+1)
  have hj := binaryWordWidth_mul (B+1) w
  have hj' := GeneralPaperRayOperandWidthEnvelope.word_add ((B+1)*w) 2
  have hsize := binaryWordWidth_mono hs
  have hsizeBound : binaryWordWidth g.size≤B+binaryWordWidth (w+1)+5 := by dsimp [J] at hsize; omega
  have h1 : binaryWordWidth 1=1 := by decide
  have hsPlus := GeneralPaperRayOperandWidthEnvelope.word_add g.size 1
  have hdepth := GeneralPaperPowerCeiling.loop_depth (g.size+1) 1 (by decide)
  change g.depth≤binaryWordWidth (g.size+1) at hdepth
  have hdepthWord := GeneralPaperInitializerControlCounters.word_le_self g.depth
  have hdw := GeneralPaperPowerCeiling.ceiling_work (g.size+1)
  change g.depthWork≤12*binaryWordWidth (g.size+1)+2 at hdw
  have hdww := GeneralPaperInitializerControlCounters.word_le_self g.depthWork
  have hscaled := scaled_work q w B
  change g.scaledWork=58*g.size+18 at hscaled
  have hsw1 := binaryWordWidth_mul 58 g.size
  have hsw2 := GeneralPaperRayOperandWidthEnvelope.word_add (58*g.size) 18
  have h58 : binaryWordWidth 58=6 := by decide
  have h18 : binaryWordWidth 18=5 := by decide
  refine ⟨hnums,hleaf,?_⟩
  change ∀ x∈[g.size,g.depth,g.profitDenominator,g.scaledWork,g.depthWork],natBits x≤word q w B
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl
  · unfold natBits word; omega
  · unfold natBits word; omega
  · exact hden
  · unfold natBits word; rw [hscaled]; omega
  · unfold natBits word; omega

def footprint {q w B : ℕ} (W : ℕ) (g : Prepared q w B) : ℕ :=
  GeneralPaperEncodedNatArray.footprint W g.numerators+GeneralPaperEncodedNatArray.footprint W g.leafNumerators+
    fields W [g.size,g.depth,g.profitDenominator,g.scaledWork,g.depthWork]+32*W

def profile (W P w B : ℕ) : ℕ := 2*((B+1)*w+2)*(P+W)+5*(P+W)+128*W

theorem native (W q w B : ℕ) : footprint W (prepare q w B)≤profile W (word q w B) w B := by
  have h := words q w B
  have hs := size_bound q w B
  have h1 := GeneralPaperEncodedNatArray.bounded_length W (word q w B) _ _ hs h.1
  have h2 := GeneralPaperEncodedNatArray.bounded_length W (word q w B) _ _ hs h.2.1
  have h3 := fields_bound W (word q w B) _ h.2.2
  change _≤5*(word q w B+W)+32*W at h3
  unfold footprint profile
  nlinarith only [h1,h2,h3]

theorem source_word (m lambda k Qv : ℕ) :
    let p := GeneralPaperProfitParameters.parameters m lambda k Qv
    word p.qProf p.width p.exponent≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have hs := GeneralPaperProfitGridEnvelope.sizes m lambda k Qv
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  have hq := hs.q
  have hw := hs.width
  have he := hs.exponent
  unfold word GeneralPaperPowerPreparationEnvelope.operandWidth
  omega

theorem source (W m lambda k Qv : ℕ) :
    let p := GeneralPaperProfitParameters.prepare m lambda k Qv
    footprint W p.grid≤profile W (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)
      p.parameters.width p.parameters.exponent := by
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  have hn := native W p.qProf p.width p.exponent
  have hm := Nat.mul_le_mul_left (2*((p.exponent+1)*p.width+2))
    (Nat.add_le_add_right (source_word m lambda k Qv) W)
  have hm' := Nat.mul_le_mul_left 5 (Nat.add_le_add_right (source_word m lambda k Qv) W)
  exact hn.trans (Nat.add_le_add_right (Nat.add_le_add hm hm') _)

end Blotto.GeneralPaperEncodedProfitGrid
