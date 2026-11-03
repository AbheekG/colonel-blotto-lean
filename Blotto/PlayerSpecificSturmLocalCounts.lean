import Blotto.PlayerSpecificFiniteJumpCount

/-! Actual computed Sturm variation counts are locally constant off the
first polynomial's roots and drop by exactly one at each simple root.
These are the executing chain's local facts for the global counting join. -/
namespace Blotto.PlayerSpecificSturmLocalCounts
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization
open PlayerSpecificSturmVariations PlayerSpecificSturmEvaluatedRules PlayerSpecificSturmLocalStability
open PlayerSpecificSquarefreeAlgorithm SignType Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable def value (p : Data) (x : ℝ) : ℕ := (evaluated (PlayerSpecificSturmSequence.run p) x).signVariations
noncomputable def tailValue (p : Data) (x : ℝ) : ℕ := (evaluated (PlayerSpecificSturmSequence.run p).tail x).signVariations

theorem mapped_evaluations (rows : List Data) (x : ℝ) :
    (rows.map realPolynomial).map (fun p => p.eval x)=evaluated rows x := by
  simp only [List.map_map,Function.comp_def,real_evaluate,evaluated]

theorem away (p : Data) (hp : semantics p≠0)
    (hs : ∀ a,(realPolynomial p).IsRoot a → ¬(realPolynomial p).derivative.IsRoot a)
    (a : ℝ) (ha : realEvaluate p a≠0) : ∀ᶠ x in 𝓝 a,value p x=value p a := by
  have hpat := run_pattern p hp hs a ha
  have hmapped : PlayerSpecificSturmPattern.Pattern
      (((PlayerSpecificSturmSequence.run p).map realPolynomial).map (fun q => q.eval a)) := by
    rw [mapped_evaluations]
    exact hpat
  have h := variations_near ((PlayerSpecificSturmSequence.run p).map realPolynomial) a hmapped
  simpa only [mapped_evaluations,value] using h

theorem tail_near_root (p : Data) (hp : semantics p≠0)
    (hs : ∀ a,(realPolynomial p).IsRoot a → ¬(realPolynomial p).derivative.IsRoot a)
    (a : ℝ) (ha : realEvaluate p a=0) : ∀ᶠ x in 𝓝 a,tailValue p x=tailValue p a := by
  have hpat := run_tail_pattern p hp hs a ha
  have hmapped : PlayerSpecificSturmPattern.Pattern
      (((PlayerSpecificSturmSequence.run p).tail.map realPolynomial).map (fun q => q.eval a)) := by
    rw [mapped_evaluations]
    exact hpat
  have h := variations_near ((PlayerSpecificSturmSequence.run p).tail.map realPolynomial) a hmapped
  simpa only [mapped_evaluations,tailValue] using h

theorem real_trim (p : Data) : realPolynomial (trim p)=realPolynomial p := by
  unfold realPolynomial
  rw [trim_semantics]

theorem real_derivative (p : Data) : realPolynomial (derivative p)=(realPolynomial p).derivative := by
  unfold realPolynomial
  rw [derivative_semantics,Polynomial.derivative_map]

theorem root_heads (p : Data) (hp : semantics p≠0) (a : ℝ) (ha : realEvaluate p a=0)
    (hs : ∀ a,(realPolynomial p).IsRoot a → ¬(realPolynomial p).derivative.IsRoot a) :
    ∃ (first second : Data) (rest : List Data),
      PlayerSpecificSturmSequence.run p=first::second::rest ∧
      realPolynomial first=realPolynomial p ∧ realPolynomial second=(realPolynomial p).derivative := by
  let first := trim p
  let second := trim (derivative first)
  have hf : first≠[] := fun h => hp ((trim_nil_iff p).mp h)
  have he0 : realPolynomial first=realPolynomial p := real_trim p
  have he1 : realPolynomial second=(realPolynomial p).derivative := by
    dsimp only [second]
    rw [real_trim,real_derivative,he0]
  have hroot : (realPolynomial p).IsRoot a := by
    change (realPolynomial p).eval a=0
    rw [real_evaluate]
    exact ha
  have hd0 := hs a hroot
  have hd : second≠[] := by
    intro hz
    apply hd0
    change (realPolynomial p).derivative.eval a=0
    rw [← he1,hz]
    simp only [realPolynomial,semantics,Polynomial.map_zero,Polynomial.eval_zero]
  cases hc : PlayerSpecificSturmSequence.chain second.length first second with
  | nil => exact False.elim (hd ((PlayerSpecificSturmSequence.empty_iff _ _ _).mp hc))
  | cons r rest =>
    have hr := PlayerSpecificSturmSequence.first second.length first second r rest hc
    subst r
    refine ⟨first,second,rest,?_,he0,he1⟩
    unfold PlayerSpecificSturmSequence.run
    dsimp only
    rw [ite_eq_right (show trim p≠[] from hf)]
    exact congrArg (List.cons first) hc

theorem sign_neg_nonzero (s : SignType) (hs : s≠0) : -s≠0 := by cases s <;> simp_all

theorem sign_neg_distinct (s : SignType) (hs : s≠0) : -s≠s := by cases s <;> simp_all

theorem jumps (p : Data) (hp : semantics p≠0)
    (hs : ∀ a,(realPolynomial p).IsRoot a → ¬(realPolynomial p).derivative.IsRoot a)
    (a : ℝ) (ha : realEvaluate p a=0) :
    ∀ᶠ x in 𝓝 a,(x<a → value p x=value p a+1) ∧ (a≤x → value p x=value p a) := by
  have hroot : (realPolynomial p).eval a=0 := by rw [real_evaluate]; exact ha
  have hd0 := hs a hroot
  have hc := PlayerSpecificSturmSignEvents.simple_crossing (realPolynomial p) a hroot hd0
  have ht := tail_near_root p hp hs a ha
  rcases root_heads p hp a ha hs with ⟨first,second,rest,hrows,hfirst,hsecond⟩
  have hf (x : ℝ) : realEvaluate first x=(realPolynomial p).eval x := by rw [← real_evaluate,hfirst]
  have hd (x : ℝ) : realEvaluate second x=(realPolynomial p).derivative.eval x := by rw [← real_evaluate,hsecond]
  have hcenter : value p a=tailValue p a := by
    simp only [value,tailValue,hrows,evaluated,List.map_cons,List.tail_cons,hf,hroot,List.signVariations_zero_cons]
  have hstep (x : ℝ) (hx0 : (realPolynomial p).eval x≠0) (hdx0 : (realPolynomial p).derivative.eval x≠0) :
      value p x=tailValue p x+(if sign ((realPolynomial p).eval x)=sign ((realPolynomial p).derivative.eval x) then 0 else 1) := by
    simp only [value,tailValue,hrows,evaluated,List.map_cons,List.tail_cons,hf,hd]
    exact List.signVariations_cons_cons_of_ne_zero _ hx0 hdx0
  filter_upwards [hc,ht] with x hcross htail
  constructor
  · intro hxa
    have hsign := hcross.2.1 hxa
    have hfirst0 : (realPolynomial p).eval x≠0 := by
      apply sign_ne_zero.mp
      rw [hsign]
      exact sign_neg_nonzero _ (sign_ne_zero.mpr hcross.1)
    have hneq : sign ((realPolynomial p).eval x)≠sign ((realPolynomial p).derivative.eval x) := by
      intro he
      exact sign_neg_distinct _ (sign_ne_zero.mpr hcross.1) (hsign.symm.trans he)
    have hcount := hstep x hfirst0 hcross.1
    rw [ite_eq_right hneq] at hcount
    rw [hcount,htail,← hcenter]
  · intro hax
    rcases lt_or_eq_of_le hax with hlt | heq
    · have hsign := hcross.2.2 hlt
      have hfirst0 : (realPolynomial p).eval x≠0 := by
        apply sign_ne_zero.mp
        rw [hsign]
        exact sign_ne_zero.mpr hcross.1
      have hcount := hstep x hfirst0 hcross.1
      rw [ite_eq_left hsign,add_zero] at hcount
      rw [hcount,htail,← hcenter]
    · subst x
      rfl

end Blotto.PlayerSpecificSturmLocalCounts
