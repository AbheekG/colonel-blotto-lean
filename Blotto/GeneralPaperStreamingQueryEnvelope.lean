import Blotto.GeneralPaperStreamingQuerySpace

/-! Both actual CF calls fit the paper's source-Lambda bound. Positive
field count is the general algorithm's branch; empty inputs retain their
separate boundary branch. Constructed parameters discharge every local
control and operand capacity, without a supplied width oracle.
-/
namespace Blotto.GeneralPaperStreamingQueryEnvelope
set_option autoImplicit false
set_option maxHeartbeats 8000000

theorem accuracy_index (m k : ℕ) (hm : 0<m) :
    k≤(GeneralPaperProxyParameters.alphabet m k).lambda := by
  have he : ∀ e : ℕ, e+1≤2^e := by
    intro e
    induction e with
    | zero => decide
    | succ e ih => rw [pow_succ]; omega
  have hp := GeneralPaperComparatorParameters.count_positive k
  have hMul := Nat.mul_le_mul_right ((GeneralPaperComparatorParameters.countRun k).power-1) (show 1≤m by omega)
  have hJ := (GeneralPaperComparatorParameters.data m k (GeneralPaperProxyParameters.prepare m k).qbar).2.1
  have hE := GeneralPaperPrecallWordEnvelope.alphabet_exponent m k
  have hk := he (17+k)
  rw [←GeneralPaperComparatorParameters.count_power] at hk
  omega

theorem control (m k : ℕ) (hm : 0<m) :
    GeneralPaperPrecallControlWord.word m k≤224+16*(GeneralPaperProxyParameters.alphabet m k).lambda := by
  have hb := GeneralPaperPrecallWordEnvelope.word_bound m k
  have hk := accuracy_index m k hm
  have hwk := GeneralPaperInitializerControlCounters.word_le_self (k+1)
  have hwl := GeneralPaperInitializerControlCounters.word_le_self ((GeneralPaperProxyParameters.alphabet m k).lambda+1)
  omega

theorem root_grid (m k : ℕ) :
    (GeneralPaperProxyParameters.prepare m k).gridBits≤(GeneralPaperProxyParameters.alphabet m k).lambda := by
  have hg := GeneralPaperPowerCeiling.loop_depth
    (4*(GeneralPaperProxyParameters.prepare m k).H*(GeneralPaperProxyParameters.prepare m k).H) 1 (by decide)
  change (GeneralPaperPowerCeiling.ceiling
    (4*(GeneralPaperProxyParameters.prepare m k).H*(GeneralPaperProxyParameters.prepare m k).H)).doublings≤_ at hg
  rw [←(GeneralPaperProxyParameters.data m k).2.2.2.2.2.1] at hg
  exact hg.trans (GeneralPaperPrecallWordEnvelope.root_target_word m k)

theorem order_word (m k : ℕ) :
    binaryWordWidth (GeneralPaperProxyParameters.alphabet m k).D≤(GeneralPaperProxyParameters.alphabet m k).lambda+1 :=
  (binaryWordWidth_mono (GeneralPaperSourceAlphabetLower.order_le_scale (GeneralPaperProxyParameters.alphabet m k))).trans
    (GeneralPaperSourceAlphabetLower.scale_width (GeneralPaperProxyParameters.alphabet m k))

theorem root_order_word (m k : ℕ) :
    binaryWordWidth (GeneralPaperProxyParameters.prepare m k).H≤(GeneralPaperProxyParameters.alphabet m k).lambda+1 :=
  (binaryWordWidth_mono (GeneralPaperPrecallWordEnvelope.root_order m k)).trans (order_word m k)

def width (m k : ℕ) : ℕ := 512+64*(GeneralPaperProxyParameters.alphabet m k).lambda

theorem source_width (m k : ℕ) (hm : 0<m) :
    GeneralPaperPrecallControlWord.word m k+GeneralPaperCFOperandPrice.width
      (GeneralPaperProxyParameters.alphabet m k).lambda (GeneralPaperProxyParameters.alphabet m k).D≤width m k := by
  have hc := control m k hm
  have hd := order_word m k
  unfold width GeneralPaperCFOperandPrice.width
  omega

theorem root_width (m k : ℕ) (hm : 0<m) :
    GeneralPaperPrecallControlWord.word m k+GeneralPaperCFOperandPrice.width
      ((GeneralPaperProxyParameters.prepare m k).gridBits+3) (GeneralPaperProxyParameters.prepare m k).H≤width m k := by
  have hc := control m k hm
  have hd := root_order_word m k
  have hg := root_grid m k
  unfold width GeneralPaperCFOperandPrice.width
  omega

theorem combine (model : RationalCostModel) (W L H : ℕ) (h : W+L≤H) :
    W+model.rat L≤model.rat H :=
  (Nat.add_le_add_right (model.word_le W) (model.rat L)).trans
    ((model.superadditive W L).trans (model.monotone h))

theorem source_space (model : RationalCostModel) (m k t : ℕ) (closed : Bool) (hm : 0<m)
    (ht : t<(GeneralPaperProxyParameters.alphabet m k).C) :
    let a := GeneralPaperProxyParameters.alphabet m k
    GeneralPaperStreamingQuerySpace.peak model (GeneralPaperPrecallControlWord.word m k) closed a.D a.C t a.lambda≤
      1024*model.rat (width m k) :=
  (GeneralPaperStreamingQuerySpace.source model m k t closed ht).trans
    (Nat.mul_le_mul_left 1024 (combine model _ _ _ (source_width m k hm)))

theorem root_space (model : RationalCostModel) (m k t : ℕ) (closed : Bool) (hm : 0<m)
    (ht : t<(GeneralPaperProxyParameters.prepare m k).Qg) :
    let r := GeneralPaperProxyParameters.prepare m k
    GeneralPaperStreamingQuerySpace.peak model (GeneralPaperPrecallControlWord.word m k) closed r.H r.Qg t (r.gridBits+3)≤
      1024*model.rat (width m k) :=
  (GeneralPaperStreamingQuerySpace.root model m k t closed ht).trans
    (Nat.mul_le_mul_left 1024 (combine model _ _ _ (root_width m k hm)))

theorem source_work (model : RationalCostModel) (m k t : ℕ) (closed : Bool) (hm : 0<m)
    (ht : t<(GeneralPaperProxyParameters.alphabet m k).C) :
    let a := GeneralPaperProxyParameters.alphabet m k
    (GeneralPaperStreamingMidpointQuery.run model (GeneralPaperPrecallControlWord.word m k) closed a.D a.C t a.lambda).2≤
      2097152*(a.lambda+3)*model.rat (width m k) := by
  let a := GeneralPaperProxyParameters.alphabet m k
  exact (GeneralPaperStreamingMidpointQuery.work model _ a.D a.C t a.lambda closed
    a.orderPositive a.scalePositive ht a.dyadic).trans
      (Nat.mul_le_mul_left _ (combine model _ _ _ (source_width m k hm)))

theorem root_work (model : RationalCostModel) (m k t : ℕ) (closed : Bool) (hm : 0<m)
    (ht : t<(GeneralPaperProxyParameters.prepare m k).Qg) :
    let r := GeneralPaperProxyParameters.prepare m k
    (GeneralPaperStreamingMidpointQuery.run model (GeneralPaperPrecallControlWord.word m k) closed r.H r.Qg t (r.gridBits+3)).2≤
      2097152*((GeneralPaperProxyParameters.alphabet m k).lambda+6)*model.rat (width m k) := by
  let r := GeneralPaperProxyParameters.prepare m k
  have h := GeneralPaperStreamingMidpointQuery.work model (GeneralPaperPrecallControlWord.word m k) r.H r.Qg t (r.gridBits+3) closed
    (GeneralPaperProxyParameters.H_positive m k) (GeneralPaperProxyParameters.grid_positive m k) ht
    (GeneralPaperProxyClassifier.grid_dyadic m k)
  have hPrice := combine model _ _ _ (root_width m k hm)
  have hg := root_grid m k
  change r.gridBits≤(GeneralPaperProxyParameters.alphabet m k).lambda at hg
  exact h.trans (Nat.mul_le_mul
    (Nat.mul_le_mul_left 2097152 (show r.gridBits+3+3≤(GeneralPaperProxyParameters.alphabet m k).lambda+6 by omega)) hPrice)

end Blotto.GeneralPaperStreamingQueryEnvelope
