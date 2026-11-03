import Blotto.GeneralPaperPrecallCachePrice
import Blotto.GeneralPaperProxyClassifier

/-! Run the actual original-budget classifier using the retained controls.
No root/score/alphabet constructor is called here. The old preparation work
field is read only when assembling the exact native result; execution work
charges quotient, root query, selection and record writes once.
-/
namespace Blotto.GeneralPaperCachedClassifier
set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable def run (m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℝ) : GeneralPaperProxyClassifier.Result × ℕ :=
  let p := c.proxy
  let location := GeneralPaperProxyQuotient.run (b*(p.Qg:ℝ)) 1 (p.gridBits+1)
  let root := GeneralPaperProxyRootQuery.lookup p.H p.Qg location.quotient (p.gridBits+3)
  let selected := GeneralPaperProxySelection.select p.Qg location.quotient
    (by dsimp only [p]; rw [hc]; exact GeneralPaperProxyParameters.grid_positive m k) b root.fraction
  (⟨location.quotient,root.fraction,selected,p.work+location.work+root.work+selected.work+24⟩,
    location.work+root.work+selected.work+64)

theorem data (m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℝ) :
    (run m k c hc b).1=GeneralPaperProxyClassifier.classify m k b := by
  subst c
  rfl

theorem work (m k : ℕ) (c : GeneralPaperPrecallCachePrice.Cache)
    (hc : c=GeneralPaperPrecallCachePrice.specification m k) (b : ℝ) (hb : 0<b ∧ b<1) :
    (run m k c hc b).2≤182*c.proxy.gridBits+1006 := by
  subst c
  have hl := GeneralPaperProxyQuotient.locate_work m k b
  have hr := GeneralPaperProxyRootQuery.real_work (GeneralPaperProxyParameters.prepare m k).H
    (GeneralPaperProxyParameters.prepare m k).Qg (GeneralPaperProxyQuotient.locate m k b).quotient
    ((GeneralPaperProxyParameters.prepare m k).gridBits+3)
    (GeneralPaperProxyParameters.H_positive m k) (GeneralPaperProxyParameters.grid_positive m k)
    (GeneralPaperProxyQuotient.locate_spec m k b hb).1 (GeneralPaperProxyClassifier.grid_dyadic m k)
  have hs := GeneralPaperProxySelection.selected_work (GeneralPaperProxyParameters.prepare m k).Qg
    (GeneralPaperProxyQuotient.locate m k b).quotient (GeneralPaperProxyParameters.grid_positive m k) b
    (GeneralPaperProxyClassifier.classify m k b).root
  change (GeneralPaperProxyQuotient.locate m k b).work+
    (GeneralPaperProxyRootQuery.lookup (GeneralPaperProxyParameters.prepare m k).H
      (GeneralPaperProxyParameters.prepare m k).Qg (GeneralPaperProxyQuotient.locate m k b).quotient
      ((GeneralPaperProxyParameters.prepare m k).gridBits+3)).work+
    (GeneralPaperProxySelection.select (GeneralPaperProxyParameters.prepare m k).Qg
      (GeneralPaperProxyQuotient.locate m k b).quotient (GeneralPaperProxyParameters.grid_positive m k) b
      (GeneralPaperProxyClassifier.classify m k b).root).work+64≤_
  change _≤182*(GeneralPaperProxyParameters.prepare m k).gridBits+1006
  omega

noncomputable def prepare (m k : ℕ) (b : ℝ) :
    ((GeneralPaperPrecallCachePrice.Cache × GeneralPaperCodeAlphabet.Alphabet) × GeneralPaperProxyClassifier.Result) × ℕ :=
  let cache := GeneralPaperPrecallCachePrice.prepare (fun _ => 1) 1 m k
  let classified := run m k cache.1.1 (GeneralPaperPrecallCachePrice.data (fun _ => 1) 1 m k) b
  ((cache.1,classified.1),cache.2+classified.2+24)

theorem prepare_data (m k : ℕ) (b : ℝ) :
    (prepare m k b).1=((GeneralPaperPrecallCachePrice.specification m k,GeneralPaperProxyParameters.alphabet m k),
      GeneralPaperProxyClassifier.classify m k b) := by
  simp only [prepare,data,GeneralPaperPrecallCachePrice.prepare_data]

theorem prepare_work (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) :
    (prepare m k b).2≤GeneralPaperPrecallCachePrice.profile (fun _ => 1) 1 m k+
      182*(GeneralPaperProxyParameters.prepare m k).gridBits+1054 := by
  have hp := GeneralPaperPrecallCachePrice.prepare_work (fun _ => 1) (by intro a b hab; rfl) 1 m k
  have hc := work m k (GeneralPaperPrecallCachePrice.prepare (fun _ => 1) 1 m k).1.1
    (GeneralPaperPrecallCachePrice.data (fun _ => 1) 1 m k) b hb
  have hGrid : (GeneralPaperPrecallCachePrice.prepare (fun _ => 1) 1 m k).1.1.proxy.gridBits=
      (GeneralPaperProxyParameters.prepare m k).gridBits := by
    rw [GeneralPaperPrecallCachePrice.prepare_data]
    rfl
  rw [hGrid] at hc
  change (GeneralPaperPrecallCachePrice.prepare (fun _ => 1) 1 m k).2+
    (run m k (GeneralPaperPrecallCachePrice.prepare (fun _ => 1) 1 m k).1.1
      (GeneralPaperPrecallCachePrice.data (fun _ => 1) 1 m k) b).2+24≤_
  change _≤182*(GeneralPaperProxyParameters.prepare m k).gridBits+1006 at hc
  omega

theorem prepare_proxy (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) :
    let c := (prepare m k b).1
    0<c.2.choice.proxy.num ∧ c.2.choice.proxy.num<c.2.choice.proxy.den ∧
      c.2.choice.proxy.den≤c.1.1.proxy.qbar ∧
      0<c.2.choice.proxy.value ∧ c.2.choice.proxy.value<1 ∧
      c.2.choice.proxy.value.den≤c.1.1.proxy.qbar := by
  rw [prepare_data]
  have hInt := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hUnit := GeneralPaperProxyClassifier.proxy_unit m k b hb
  exact ⟨hInt.1,hInt.2.1,hInt.2.2,hUnit.1,hUnit.2,GeneralPaperProxyClassifier.proxy_reduced_denominator m k b⟩

end Blotto.GeneralPaperCachedClassifier
