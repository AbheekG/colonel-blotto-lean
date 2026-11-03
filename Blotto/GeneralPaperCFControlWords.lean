import Blotto.GeneralPaperCFPrefixCounters

/-! A logarithmic control word for every reached CF prefix/advance and
adaptive-division return counter. Large quotients and continuants remain
separately priced arithmetic operands; only small metadata uses this word.
-/
namespace Blotto.GeneralPaperCFControlWords
open GeneralPaperRegularCFLoop
set_option autoImplicit false
set_option maxHeartbeats 6000000

def cap (lambda : ℕ) : ℕ := 512*(lambda+1)+4096
def width (lambda : ℕ) : ℕ := 64+binaryWordWidth (lambda+1)

theorem cap_word (lambda : ℕ) : binaryWordWidth (cap lambda)≤width lambda := by
  have hm := binaryWordWidth_mul 512 (lambda+1)
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (512*(lambda+1)) 4096
  have h512 : binaryWordWidth 512=10 := by decide
  have h4096 : binaryWordWidth 4096=13 := by decide
  unfold cap width
  omega

theorem bounded (lambda n : ℕ) (hn : n≤cap lambda) : binaryWordWidth n≤width lambda :=
  (binaryWordWidth_mono hn).trans (cap_word lambda)

theorem mono {a b : ℕ} (h : a≤b) : width a≤width b := by
  have hh := binaryWordWidth_mono (Nat.add_le_add_right h 1)
  unfold width
  omega

theorem prefix_words (D C t lambda fuel : ℕ) (hD : 0<D) (hC : 0<C) (ht : t<C)
    (hPower : 8*C=2^lambda) (hFuel : fuel≤2*lambda+4) :
    let s := run D (lambda+2) fuel (initial C t)
    binaryWordWidth (s.steps+1)≤width lambda ∧ binaryWordWidth (s.quotientDepth+lambda+2)≤width lambda ∧
    binaryWordWidth (s.zeroChecks+1)≤width lambda ∧ binaryWordWidth (s.work+512)≤width lambda := by
  have hb := GeneralPaperCFPrefixCounters.prefix_bounds D C t lambda fuel hD hC ht hPower hFuel
  dsimp only at hb ⊢
  refine ⟨bounded lambda _ ?_,bounded lambda _ ?_,bounded lambda _ ?_,bounded lambda _ ?_⟩ <;>
    unfold cap <;> omega

theorem returned_advance (D C t lambda fuel : ℕ) (hD : 0<D) (hC : 0<C) (ht : t<C)
    (hPower : 8*C=2^lambda) (hFuel : fuel≤2*lambda+4) :
    let s := (advance D (lambda+2) (run D (lambda+2) fuel (initial C t))).1
    binaryWordWidth (s.steps+1)≤width lambda ∧ binaryWordWidth (s.quotientDepth+1)≤width lambda ∧
    binaryWordWidth (s.zeroChecks+1)≤width lambda ∧ binaryWordWidth (s.work+64)≤width lambda := by
  have hb := GeneralPaperCFPrefixCounters.advance_bounds D C t lambda fuel hD hC ht hPower hFuel
  dsimp only at hb ⊢
  refine ⟨bounded lambda _ ?_,bounded lambda _ ?_,bounded lambda _ ?_,bounded lambda _ ?_⟩ <;>
    unfold cap <;> omega

theorem fuel_words (lambda fuel divisionFuel : ℕ) (hFuel : fuel≤2*lambda+4) (hDivision : divisionFuel≤lambda+2) :
    binaryWordWidth fuel≤width lambda ∧ binaryWordWidth divisionFuel≤width lambda ∧
    binaryWordWidth (lambda+2)≤width lambda ∧ binaryWordWidth (2*lambda+4)≤width lambda := by
  refine ⟨bounded lambda _ ?_,bounded lambda _ ?_,bounded lambda _ ?_,bounded lambda _ ?_⟩ <;>
    unfold cap <;> omega

theorem growing_return (primitive : ℕ → ℕ) (W lambda n d fuel : ℕ) (hFuel : fuel≤lambda+2) :
    binaryWordWidth ((GeneralPaperGrowingQuotientBits.run primitive W n d fuel).1.depth+1)≤width lambda ∧
    binaryWordWidth ((GeneralPaperGrowingQuotientBits.run primitive W n d fuel).1.work+14)≤width lambda := by
  rw [GeneralPaperGrowingQuotientBits.data]
  have hb := GeneralPaperNaturalGrowingQuotient.counters n d fuel
  refine ⟨bounded lambda _ ?_,bounded lambda _ ?_⟩ <;> unfold cap <;> omega

theorem division_return (primitive : ℕ → ℕ) (W lambda n d fuel : ℕ) (hFuel : fuel≤lambda+2) :
    binaryWordWidth ((GeneralPaperConstructedNatDivisionBits.run primitive W n d fuel).1.depth+1)≤width lambda ∧
    binaryWordWidth ((GeneralPaperConstructedNatDivisionBits.run primitive W n d fuel).1.work+48)≤width lambda := by
  rw [GeneralPaperConstructedNatDivisionBits.data]
  have hb := GeneralPaperCFPrefixCounters.division_counters n d fuel
  refine ⟨bounded lambda _ ?_,bounded lambda _ ?_⟩ <;> unfold cap <;> omega

end Blotto.GeneralPaperCFControlWords
