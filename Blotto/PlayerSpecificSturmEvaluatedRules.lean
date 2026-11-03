import Blotto.PlayerSpecificSturmLocalStability

/-! The actually computed rational chain obeys the real evaluated Sturm
rules. Squarefree preprocessing discharges the no-common-root condition
for all real points; the resulting sign patterns cover internal zeroes. -/
namespace Blotto.PlayerSpecificSturmEvaluatedRules
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificSturmLocalStability
set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable def evaluated (rows : List Data) (x : ℝ) : List ℝ := rows.map (fun p => realEvaluate p x)
def NoCommonAt (p q : Data) (x : ℝ) : Prop := ¬(realEvaluate p x=0 ∧ realEvaluate q x=0)

theorem eval_trim (p : Data) (x : ℝ) : realEvaluate (trim p) x=realEvaluate p x := by
  rw [← realEvaluate_semantics,← realEvaluate_semantics,trim_semantics]

theorem eval_derivative (p : Data) (x : ℝ) :
    realEvaluate (derivative p) x=(PlayerSpecificSquarefreeAlgorithm.realPolynomial p).derivative.eval x := by
  rw [← PlayerSpecificSquarefreeAlgorithm.real_evaluate]
  change ((semantics (derivative p)).map (Rat.castHom ℝ)).eval x=_
  rw [derivative_semantics,← Polynomial.derivative_map]
  rfl

theorem next_identity (p q : Data) (x : ℝ) :
    realEvaluate p x=realEvaluate q x*realEvaluate (PlayerSpecificPolynomialDivision.run p q).1 x-
      realEvaluate (PlayerSpecificSturmSequence.next p q) x := by
  have h := congrArg (fun f : Polynomial ℚ => f.eval₂ (Rat.castHom ℝ) x) (PlayerSpecificSturmSequence.next_identity p q)
  simpa only [Polynomial.eval₂_mul,Polynomial.eval₂_sub,realEvaluate_semantics] using h

theorem next_no_common (p q : Data) (x : ℝ) (h : NoCommonAt p q x) :
    NoCommonAt q (PlayerSpecificSturmSequence.next p q) x := by
  rintro ⟨hq,hn⟩
  apply h ⟨?_,hq⟩
  rw [next_identity p q x,hq,hn,zero_mul,sub_self]

theorem chain_rules (fuel : ℕ) (p q : Data) (x : ℝ) (hq : Normalized q) (hcap : q.length≤fuel)
    (hn : NoCommonAt p q x) :
    RulesFrom (realEvaluate p x) (evaluated (PlayerSpecificSturmSequence.chain fuel p q) x) := by
  induction fuel generalizing p q with
  | zero =>
    have hz : q=[] := List.length_eq_zero_iff.mp (by omega)
    subst q
    simp only [PlayerSpecificSturmSequence.chain,ite_true,evaluated,List.map_nil,RulesFrom]
    exact fun h => hn ⟨h,rfl⟩
  | succ fuel ih =>
    rw [PlayerSpecificSturmSequence.chain]
    split
    · rename_i hz
      subst q
      simp only [evaluated,List.map_nil,RulesFrom]
      exact fun h => hn ⟨h,rfl⟩
    · rename_i hq0
      have hdrop := PlayerSpecificSturmSequence.next_length p q hq hq0
      have ht := ih q (PlayerSpecificSturmSequence.next p q) (PlayerSpecificSturmSequence.next_normalized p q)
        (by omega) (next_no_common p q x hn)
      have hadj : realEvaluate p x≠0 ∨ realEvaluate q x≠0 := by
        by_cases hp : realEvaluate p x=0
        · exact Or.inr (fun hq' => hn ⟨hp,hq'⟩)
        · exact Or.inl hp
      change RulesFrom (realEvaluate p x) (realEvaluate q x::evaluated (PlayerSpecificSturmSequence.chain fuel q
        (PlayerSpecificSturmSequence.next p q)) x)
      refine ⟨hadj,ht,?_⟩
      cases he : PlayerSpecificSturmSequence.chain fuel q (PlayerSpecificSturmSequence.next p q) with
      | nil => trivial
      | cons r rest =>
        have hr := PlayerSpecificSturmSequence.first fuel q (PlayerSpecificSturmSequence.next p q) r rest he
        change realEvaluate q x=0 → realEvaluate p x = -realEvaluate r x
        intro hz
        rw [hr]
        have h := next_identity p q x
        rw [hz,zero_mul,zero_sub] at h
        exact h

theorem no_common_derivative (p : Data)
    (hs : ∀ a,(PlayerSpecificSquarefreeAlgorithm.realPolynomial p).IsRoot a →
      ¬(PlayerSpecificSquarefreeAlgorithm.realPolynomial p).derivative.IsRoot a) (x : ℝ) :
    NoCommonAt p (trim (derivative p)) x := by
  rintro ⟨hp,hd⟩
  apply hs x
  · change (PlayerSpecificSquarefreeAlgorithm.realPolynomial p).eval x=0
    rw [PlayerSpecificSquarefreeAlgorithm.real_evaluate]
    exact hp
  · change (PlayerSpecificSquarefreeAlgorithm.realPolynomial p).derivative.eval x=0
    rw [eval_trim,eval_derivative] at hd
    exact hd

theorem run_pattern (p : Data) (hp : semantics p≠0)
    (hs : ∀ a,(PlayerSpecificSquarefreeAlgorithm.realPolynomial p).IsRoot a →
      ¬(PlayerSpecificSquarefreeAlgorithm.realPolynomial p).derivative.IsRoot a)
    (x : ℝ) (hx : realEvaluate p x≠0) :
    PlayerSpecificSturmPattern.Pattern (evaluated (PlayerSpecificSturmSequence.run p) x) := by
  have hfirst : trim p≠[] := fun h => hp ((trim_nil_iff p).mp h)
  have heq : PlayerSpecificSquarefreeAlgorithm.realPolynomial (trim p)=PlayerSpecificSquarefreeAlgorithm.realPolynomial p := by
    unfold PlayerSpecificSquarefreeAlgorithm.realPolynomial
    rw [trim_semantics]
  have hsimple : ∀ a,(PlayerSpecificSquarefreeAlgorithm.realPolynomial (trim p)).IsRoot a →
      ¬(PlayerSpecificSquarefreeAlgorithm.realPolynomial (trim p)).derivative.IsRoot a := by rw [heq]; exact hs
  have hr := chain_rules (trim (derivative (trim p))).length (trim p) (trim (derivative (trim p))) x
    (trim_normalized _) le_rfl (no_common_derivative (trim p) hsimple x)
  have hpat := pattern (realEvaluate (trim p) x) _ hr (by rw [eval_trim]; exact hx)
  simpa only [PlayerSpecificSturmSequence.run,ite_eq_right hfirst,evaluated,List.map_cons] using hpat

theorem tail_pattern (a : ℝ) (rest : List ℝ) (hr : RulesFrom a rest) (ha : a=0) :
    PlayerSpecificSturmPattern.Pattern rest := by
  cases rest with
  | nil => rw [PlayerSpecificSturmPattern.Pattern.eq_def]; trivial
  | cons b tail =>
    have hb := hr.1.resolve_left (not_not.mpr ha)
    exact pattern b tail hr.2.1 hb

theorem run_tail_pattern (p : Data) (hp : semantics p≠0)
    (hs : ∀ a,(PlayerSpecificSquarefreeAlgorithm.realPolynomial p).IsRoot a →
      ¬(PlayerSpecificSquarefreeAlgorithm.realPolynomial p).derivative.IsRoot a)
    (x : ℝ) (hx : realEvaluate p x=0) :
    PlayerSpecificSturmPattern.Pattern (evaluated (PlayerSpecificSturmSequence.run p).tail x) := by
  have hfirst : trim p≠[] := fun h => hp ((trim_nil_iff p).mp h)
  have heq : PlayerSpecificSquarefreeAlgorithm.realPolynomial (trim p)=PlayerSpecificSquarefreeAlgorithm.realPolynomial p := by
    unfold PlayerSpecificSquarefreeAlgorithm.realPolynomial
    rw [trim_semantics]
  have hsimple : ∀ a,(PlayerSpecificSquarefreeAlgorithm.realPolynomial (trim p)).IsRoot a →
      ¬(PlayerSpecificSquarefreeAlgorithm.realPolynomial (trim p)).derivative.IsRoot a := by rw [heq]; exact hs
  have hr := chain_rules (trim (derivative (trim p))).length (trim p) (trim (derivative (trim p))) x
    (trim_normalized _) le_rfl (no_common_derivative (trim p) hsimple x)
  have hpat := tail_pattern (realEvaluate (trim p) x) _ hr (by rw [eval_trim]; exact hx)
  simpa only [PlayerSpecificSturmSequence.run,ite_eq_right hfirst,List.tail_cons] using hpat

end Blotto.PlayerSpecificSturmEvaluatedRules
