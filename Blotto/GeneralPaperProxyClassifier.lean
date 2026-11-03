import Blotto.GeneralPaperProxySelectionUnit

/-! Actual pre-call proxy classifier: constructed root grid, real budget
quotient, last bounded convergent with inclusive tests, then the seven
selection branches. No root or denominator-cap oracle is supplied.
Residual determinant interpretation, root-free transfer paths, bit/space
prices and original-unit continuation remain separate obligations.
-/
namespace Blotto.GeneralPaperProxyClassifier
open GeneralPaperProxyParameters GeneralPaperProxySelection
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Result where
  cell : ℕ
  root : Option Farey.Fraction
  choice : Selected
  work : ℕ

noncomputable def classify (m k : ℕ) (b : ℝ) : Result :=
  let p := prepare m k
  let location := GeneralPaperProxyQuotient.run (b*(p.Qg:ℝ)) 1 (p.gridBits+1)
  let root := GeneralPaperProxyRootQuery.lookup p.H p.Qg location.quotient (p.gridBits+3)
  let selected := select p.Qg location.quotient (grid_positive m k) b root.fraction
  ⟨location.quotient,root.fraction,selected,p.work+location.work+root.work+selected.work+24⟩

theorem grid_dyadic (m k : ℕ) : 8*(prepare m k).Qg=2^((prepare m k).gridBits+3) := by
  rw [grid_power,pow_add]
  norm_num
  omega

theorem root_sound (m k : ℕ) (b : ℝ) (f : Farey.Fraction) (hf : (classify m k b).root=some f) :
    f.den≤(prepare m k).H ∧ GeneralPaperProxyCell.Closed (prepare m k).Qg (classify m k b).cell f.value :=
  GeneralPaperProxyRootQuery.sound _ _ _ _ f hf

theorem root_none (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) :
    (classify m k b).root=none ↔ ∀ f : Farey.Fraction, f.den≤(prepare m k).H →
      ¬GeneralPaperProxyCell.Closed (prepare m k).Qg (classify m k b).cell f.value :=
  GeneralPaperProxyRootQuery.none_iff _ _ _ _ (H_positive m k) (grid_positive m k)
    (GeneralPaperProxyQuotient.locate_spec m k b hb).1 (grid_lower m k) (grid_dyadic m k)

theorem proxy_unit (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) :
    0<(classify m k b).choice.proxy.value ∧ (classify m k b).choice.proxy.value<1 :=
  GeneralPaperProxySelectionUnit.selected_unit _ _ _ (H_positive m k) (grid_positive m k) (grid_lower m k)
    (GeneralPaperProxyQuotient.locate_spec m k b hb).1 b hb _ (root_sound m k b)

theorem proxy_denominator (m k : ℕ) (b : ℝ) : (classify m k b).choice.proxy.den≤(prepare m k).qbar := by
  have hH := H_positive m k
  have hg := grid_lower m k
  have hc : (prepare m k).H≤2*(prepare m k).Qg := by nlinarith
  rw [(data m k).2.2.2.2.2.2]
  exact denominator_bound _ _ _ (grid_positive m k) hc b _ (fun f hf => (root_sound m k b f hf).1)

theorem proxy_reduced_denominator (m k : ℕ) (b : ℝ) :
    (classify m k b).choice.proxy.value.den≤(prepare m k).qbar :=
  (Farey.value_den_le _).trans (proxy_denominator m k b)

theorem proxy_integer_representation (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) :
    0<(classify m k b).choice.proxy.num ∧
      (classify m k b).choice.proxy.num<(classify m k b).choice.proxy.den ∧
      (classify m k b).choice.proxy.den≤(prepare m k).qbar := by
  let f := (classify m k b).choice.proxy
  have hu := proxy_unit m k b hb
  change 0<f.value ∧ f.value<1 at hu
  have hd : (0:ℚ)<f.den := by exact_mod_cast f.den_pos
  have he : (f.num:ℚ)=f.value*(f.den:ℚ) := by
    unfold Farey.Fraction.value
    exact (div_mul_cancel₀ _ hd.ne').symm
  have hn : (0:ℚ)<f.num := by rw [he]; exact mul_pos hu.1 hd
  have hl : (f.num:ℚ)<f.den := (div_lt_one hd).mp hu.2
  exact ⟨by exact_mod_cast hn,by exact_mod_cast hl,proxy_denominator m k b⟩

theorem classify_work (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) :
    (classify m k b).work≤(prepare m k).work+182*(prepare m k).gridBits+966 := by
  have hl := GeneralPaperProxyQuotient.locate_work m k b
  have hr := GeneralPaperProxyRootQuery.real_work (prepare m k).H (prepare m k).Qg
    (GeneralPaperProxyQuotient.locate m k b).quotient ((prepare m k).gridBits+3)
    (H_positive m k) (grid_positive m k) (GeneralPaperProxyQuotient.locate_spec m k b hb).1 (grid_dyadic m k)
  have hs := selected_work (prepare m k).Qg (GeneralPaperProxyQuotient.locate m k b).quotient
    (grid_positive m k) b (classify m k b).root
  change (prepare m k).work+(GeneralPaperProxyQuotient.locate m k b).work+
    (GeneralPaperProxyRootQuery.lookup (prepare m k).H (prepare m k).Qg
      (GeneralPaperProxyQuotient.locate m k b).quotient ((prepare m k).gridBits+3)).work+
    (select (prepare m k).Qg (GeneralPaperProxyQuotient.locate m k b).quotient
      (grid_positive m k) b (classify m k b).root).work+24≤_
  omega

end Blotto.GeneralPaperProxyClassifier
