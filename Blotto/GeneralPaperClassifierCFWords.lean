import Blotto.GeneralPaperClassifierControlWords

/-! Transfer all remaining generic CF return/fuel word bounds to either
actual classifier root grid or actual selected source alphabet. The common
word is constructed once and no local capacity premise remains supplied.
-/
namespace Blotto.GeneralPaperClassifierCFWords
open GeneralPaperPrecallControlWord
set_option autoImplicit false

def QueryWidth (m k lambda : ℕ) : Prop :=
  lambda=(GeneralPaperProxyParameters.prepare m k).gridBits+3 ∨
  lambda=(GeneralPaperProxyParameters.alphabet m k).lambda

theorem calibrated (m k lambda : ℕ) (h : QueryWidth m k lambda) :
    GeneralPaperCFControlWords.width lambda≤word m k := by
  rcases h with h|h
  · rw [h]; exact GeneralPaperPrecallLoopWords.root_CF m k
  · rw [h]; exact GeneralPaperPrecallLoopWords.source_CF m k

theorem division_returns (primitive : ℕ → ℕ) (m k lambda n d fuel : ℕ)
    (h : QueryWidth m k lambda) (hFuel : fuel≤lambda+2) :
    binaryWordWidth ((GeneralPaperGrowingQuotientBits.run primitive (word m k) n d fuel).1.depth+1)≤word m k ∧
    binaryWordWidth ((GeneralPaperGrowingQuotientBits.run primitive (word m k) n d fuel).1.work+14)≤word m k ∧
    binaryWordWidth ((GeneralPaperConstructedNatDivisionBits.run primitive (word m k) n d fuel).1.depth+1)≤word m k ∧
    binaryWordWidth ((GeneralPaperConstructedNatDivisionBits.run primitive (word m k) n d fuel).1.work+48)≤word m k := by
  have hw := calibrated m k lambda h
  have hg := GeneralPaperCFControlWords.growing_return primitive (word m k) lambda n d fuel hFuel
  have hd := GeneralPaperCFControlWords.division_return primitive (word m k) lambda n d fuel hFuel
  exact ⟨hg.1.trans hw,hg.2.trans hw,hd.1.trans hw,hd.2.trans hw⟩

theorem fuel_words (m k lambda fuel divisionFuel : ℕ) (h : QueryWidth m k lambda)
    (hFuel : fuel≤2*lambda+4) (hDivision : divisionFuel≤lambda+2) :
    binaryWordWidth fuel≤word m k ∧ binaryWordWidth divisionFuel≤word m k ∧
    binaryWordWidth (lambda+2)≤word m k ∧ binaryWordWidth (2*lambda+4)≤word m k := by
  have hw := calibrated m k lambda h
  have hc := GeneralPaperCFControlWords.fuel_words lambda fuel divisionFuel hFuel hDivision
  exact ⟨hc.1.trans hw,hc.2.1.trans hw,hc.2.2.1.trans hw,hc.2.2.2.trans hw⟩

theorem root_advance (m k j fuel : ℕ) (hj : j<(GeneralPaperProxyParameters.prepare m k).Qg)
    (hFuel : fuel≤2*((GeneralPaperProxyParameters.prepare m k).gridBits+3)+4) :
    let r := GeneralPaperProxyParameters.prepare m k
    let s := (GeneralPaperRegularCFLoop.advance r.H (r.gridBits+3+2)
      (GeneralPaperRegularCFLoop.run r.H (r.gridBits+3+2) fuel (GeneralPaperRegularCFLoop.initial r.Qg j))).1
    binaryWordWidth (s.steps+1)≤word m k ∧ binaryWordWidth (s.quotientDepth+1)≤word m k ∧
    binaryWordWidth (s.zeroChecks+1)≤word m k ∧ binaryWordWidth (s.work+64)≤word m k := by
  have hc := GeneralPaperCFControlWords.returned_advance (GeneralPaperProxyParameters.prepare m k).H
    (GeneralPaperProxyParameters.prepare m k).Qg j ((GeneralPaperProxyParameters.prepare m k).gridBits+3) fuel
    (GeneralPaperProxyParameters.H_positive m k) (GeneralPaperProxyParameters.grid_positive m k) hj
    (GeneralPaperProxyClassifier.grid_dyadic m k) hFuel
  have hw := GeneralPaperPrecallLoopWords.root_CF m k
  dsimp only at hc ⊢
  exact ⟨hc.1.trans hw,hc.2.1.trans hw,hc.2.2.1.trans hw,hc.2.2.2.trans hw⟩

theorem source_advance (m k j fuel : ℕ) (hj : j<(GeneralPaperProxyParameters.alphabet m k).C)
    (hFuel : fuel≤2*(GeneralPaperProxyParameters.alphabet m k).lambda+4) :
    let a := GeneralPaperProxyParameters.alphabet m k
    let s := (GeneralPaperRegularCFLoop.advance a.D (a.lambda+2)
      (GeneralPaperRegularCFLoop.run a.D (a.lambda+2) fuel (GeneralPaperRegularCFLoop.initial a.C j))).1
    binaryWordWidth (s.steps+1)≤word m k ∧ binaryWordWidth (s.quotientDepth+1)≤word m k ∧
    binaryWordWidth (s.zeroChecks+1)≤word m k ∧ binaryWordWidth (s.work+64)≤word m k := by
  let a := GeneralPaperProxyParameters.alphabet m k
  have hc := GeneralPaperCFControlWords.returned_advance a.D a.C j a.lambda fuel
    a.orderPositive a.scalePositive hj a.dyadic hFuel
  have hw := GeneralPaperPrecallLoopWords.source_CF m k
  dsimp only at hc ⊢
  exact ⟨hc.1.trans hw,hc.2.1.trans hw,hc.2.2.1.trans hw,hc.2.2.2.trans hw⟩

end Blotto.GeneralPaperClassifierCFWords
