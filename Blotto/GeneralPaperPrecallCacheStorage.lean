import Blotto.GeneralPaperEncodedScalarStorage
import Blotto.GeneralPaperPrecallWordEnvelope
import Blotto.GeneralPaperParameterOperandBounds

/-! Erased sizes of every retained precall parameter field. Alphabet integers
have full constructed width; the logarithmic control word is not used as a
payload bound. Zero fields are allowed. No encoding traversal executes. -/
namespace Blotto.GeneralPaperPrecallCacheStorage
open GeneralPaperEncodedScalarStorage GeneralPaperPrecallCachePrice
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def payload (m k : ℕ) : ℕ := 65536*(GeneralPaperPrecallControlWord.measure m k+1)

theorem small (m k n : ℕ) (hn : n≤256*GeneralPaperPrecallControlWord.measure m k+1024) :
    natBits n≤payload m k := by
  have hw := GeneralPaperInitializerControlCounters.word_le_self n
  unfold natBits payload
  omega

theorem words (m k : ℕ) :
    let c := specification m k
    (∀ x∈[c.score.K,c.score.S,c.score.depth,c.score.work],natBits x≤payload m k) ∧
    (∀ x∈[c.proxy.K,c.proxy.S,c.proxy.d,c.proxy.H,c.proxy.Qg,c.proxy.gridBits,c.proxy.qbar,c.proxy.work],
      natBits x≤payload m k) ∧
    (∀ x∈[c.comparator.Kc,c.comparator.J,c.comparator.D,c.comparator.C,c.comparator.lambda,c.comparator.work],
      natBits x≤payload m k) := by
  let s := GeneralPaperScoreScaleParameters.prepare m k
  let r := GeneralPaperProxyParameters.prepare m k
  let a := GeneralPaperComparatorParameters.prepare m k r.qbar
  let M := GeneralPaperPrecallControlWord.measure m k
  have ht := GeneralPaperPrecallControlWord.terms m k
  have hs := GeneralPaperPrecallControlWord.score_controls m k
  have hr := GeneralPaperPrecallControlWord.root_controls m k
  have ha := GeneralPaperPrecallControlWord.alphabet_controls m k
  change k+18≤M ∧ binaryWordWidth (m*s.K)+1≤M ∧ binaryWordWidth (r.d+2)+1≤M ∧
    binaryWordWidth (4*r.H*r.H)+1≤M ∧ binaryWordWidth a.J+1≤M ∧
    binaryWordWidth (4*a.D*a.D)+1≤M ∧ r.gridBits+4≤M at ht
  change s.depth≤M ∧ s.work≤20*M+20 at hs
  change r.gridBits+4≤M ∧ r.work≤44*M+56 at hr
  change a.lambda≤M+2 ∧ a.work≤32*M+38 at ha
  have hK0 := GeneralPaperParameterOperandBounds.dyadic_word (7+k)
  have hK : natBits s.K≤payload m k := by
    change binaryWordWidth s.K≤1+2*(7+k) at hK0
    unfold natBits payload
    change _≤65536*(M+1)
    omega
  have hS0 := GeneralPaperParameterOperandBounds.ceiling_word (m*s.K)
  have hS : natBits s.S≤payload m k := by
    change binaryWordWidth s.S≤4+binaryWordWidth (m*s.K) at hS0
    unfold natBits payload
    change _≤65536*(M+1)
    omega
  have hd0 := binaryWordWidth_mono (show r.d≤r.d+2 by omega)
  have hd : natBits r.d≤payload m k := by
    unfold natBits payload
    change _≤65536*(M+1)
    omega
  have hHpos : 0<r.H := GeneralPaperProxyParameters.H_positive m k
  have hHsmall : r.H≤4*r.H*r.H := by nlinarith only [hHpos]
  have hH0 := binaryWordWidth_mono hHsmall
  have hH : natBits r.H≤payload m k := by
    unfold natBits payload
    change _≤65536*(M+1)
    omega
  have hQ0 := GeneralPaperParameterOperandBounds.ceiling_word (4*r.H*r.H)
  have hQeq : r.Qg=(GeneralPaperPowerCeiling.ceiling (4*r.H*r.H)).power :=
    (GeneralPaperProxyParameters.data m k).2.2.2.2.1
  rw [←hQeq] at hQ0
  have hQ : natBits r.Qg≤payload m k := by
    unfold natBits payload
    change _≤65536*(M+1)
    omega
  have hqeq : r.qbar=2*r.Qg := (GeneralPaperProxyParameters.data m k).2.2.2.2.2.2
  have hq0 := binaryWordWidth_mul 2 r.Qg
  have h2 : binaryWordWidth 2=2 := by decide
  have hq : natBits r.qbar≤payload m k := by
    rw [hqeq]
    unfold natBits payload
    change _≤65536*(M+1)
    omega
  have hKc0 := GeneralPaperParameterOperandBounds.dyadic_word (17+k)
  have hKc : natBits a.Kc≤payload m k := by
    change binaryWordWidth a.Kc≤1+2*(17+k) at hKc0
    unfold natBits payload
    change _≤65536*(M+1)
    omega
  have hJ : natBits a.J≤payload m k := by
    unfold natBits payload
    change _≤65536*(M+1)
    omega
  have hDpos : 0<a.D := GeneralPaperComparatorParameters.denominator_positive m k r.qbar
    (GeneralPaperProxyParameters.cap_positive m k)
  have hD0 := binaryWordWidth_mono (show a.D≤4*a.D*a.D by nlinarith only [hDpos])
  have hD : natBits a.D≤payload m k := by
    unfold natBits payload
    change _≤65536*(M+1)
    omega
  have hC0 := GeneralPaperParameterOperandBounds.ceiling_word (4*a.D*a.D)
  have hCeq : a.C=(GeneralPaperPowerCeiling.ceiling (4*a.D*a.D)).power :=
    (GeneralPaperComparatorParameters.data m k r.qbar).2.2.2.1
  rw [←hCeq] at hC0
  have hC : natBits a.C≤payload m k := by
    unfold natBits payload
    change _≤65536*(M+1)
    omega
  have controls (n : ℕ) (hn : n≤256*M+1024) : natBits n≤payload m k := small m k n hn
  change (∀ x∈[s.K,s.S,s.depth,s.work],natBits x≤payload m k) ∧
    (∀ x∈[r.K,r.S,r.d,r.H,r.Qg,r.gridBits,r.qbar,r.work],natBits x≤payload m k) ∧
    (∀ x∈[a.Kc,a.J,a.D,a.C,a.lambda,a.work],natBits x≤payload m k)
  have hrK : r.K=s.K := (GeneralPaperProxyParameters.data m k).1
  have hrS : r.S=s.S := (GeneralPaperProxyParameters.data m k).2.1
  refine ⟨?_,?_,?_⟩ <;> intro x hx <;>
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  · rcases hx with rfl|rfl|rfl|rfl
    · exact hK
    · exact hS
    · exact controls _ (by omega)
    · exact controls _ (by omega)
  · rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · rw [hrK]; exact hK
    · rw [hrS]; exact hS
    · exact hd
    · exact hH
    · exact hQ
    · exact controls _ (by omega)
    · exact hq
    · exact controls _ (by omega)
  · rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
    · exact hKc
    · exact hJ
    · exact hD
    · exact hC
    · exact controls _ (by omega)
    · exact controls _ (by omega)

def footprint (W : ℕ) (c : Cache) : ℕ :=
  fields W [c.score.K,c.score.S,c.score.depth,c.score.work]+
    fields W [c.proxy.K,c.proxy.S,c.proxy.d,c.proxy.H,c.proxy.Qg,c.proxy.gridBits,c.proxy.qbar,c.proxy.work]+
    fields W [c.comparator.Kc,c.comparator.J,c.comparator.D,c.comparator.C,c.comparator.lambda,c.comparator.work]+64*W

def alphabetFootprint (W : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) : ℕ :=
  fields W [a.D,a.C,a.lambda]+64*W

theorem native (W m k : ℕ) : footprint W (specification m k)≤18*(payload m k+W)+160*W := by
  have h := words m k
  have hs := fields_bound W (payload m k) _ h.1
  have hr := fields_bound W (payload m k) _ h.2.1
  have ha := fields_bound W (payload m k) _ h.2.2
  change _≤4*(payload m k+W)+32*W at hs
  change _≤8*(payload m k+W)+32*W at hr
  change _≤6*(payload m k+W)+32*W at ha
  unfold footprint
  omega

theorem alphabet (W m k : ℕ) : alphabetFootprint W (GeneralPaperProxyParameters.alphabet m k)≤
    3*(payload m k+W)+96*W := by
  have h := (words m k).2.2
  have hs := fields_bound W (payload m k)
    [(GeneralPaperProxyParameters.alphabet m k).D,(GeneralPaperProxyParameters.alphabet m k).C,
      (GeneralPaperProxyParameters.alphabet m k).lambda] (by
        intro x hx
        apply h x
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
        rcases hx with hx|hx|hx <;> tauto)
  change _≤3*(payload m k+W)+32*W at hs
  unfold alphabetFootprint
  omega

theorem returned (primitive : ℕ → ℕ) (W m k : ℕ) :
    footprint W (GeneralPaperPrecallCachePrice.prepare primitive W m k).1.1+
      alphabetFootprint W (GeneralPaperPrecallCachePrice.prepare primitive W m k).1.2≤
        21*(payload m k+W)+256*W := by
  rw [GeneralPaperPrecallCachePrice.prepare_data]
  dsimp only
  have h := native W m k
  have ha := alphabet W m k
  omega

theorem source_payload (m k : ℕ) :
    payload m k≤65536*(k+8*(GeneralPaperProxyParameters.alphabet m k).lambda+65) := by
  have h := GeneralPaperPrecallWordEnvelope.measure_bound m k
  unfold payload
  omega

end Blotto.GeneralPaperPrecallCacheStorage
