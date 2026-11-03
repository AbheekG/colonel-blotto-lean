import Blotto.GeneralPaperContinuousResponseRow

/-! A real feasible deviation gives a singleton feasible literal response
law. The selected physical row has exactly the original shares against any
actually decoded closed candidate, and its hard budget follows from the
paper's selected denominator-gap transfer.
-/
namespace Blotto.GeneralPaperContinuousResponseMixture
open scoped BigOperators Classical
open GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def response {m : ℕ} (a : Alphabet) (B : ℚ) (hB : B≤1) (y : Allocation m) (hy : Blotto.Feasible (B:ℝ) y) :
    GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a true B where
  law := {
    labels := 1
    weight := fun _ => 1
    rows := fun _ j => ⟨(GeneralPaperContinuousResponseRow.codes a B hB y hy).read j,GeneralPaperContinuousResponseRow.code_bound a B hB y hy j⟩
    nonnegative := by intro l; norm_num
    total := by simp }
  choices := fun _ => GeneralPaperContinuousResponseRow.choices a B hB y hy
  decoded := fun _ j => GeneralPaperContinuousResponseRow.decoded a B hB y hy j
  budget := fun _ => GeneralPaperContinuousResponseRow.tag_budget a B hB y hy

noncomputable def physicalRow {m : ℕ} (a : Alphabet) (B : ℚ) (hB : B≤1) (y : Allocation m) (hy : Blotto.Feasible (B:ℝ) y) (qbar : ℕ) : Allocation m :=
  fun j => (((GeneralPaperContinuousResponseRow.choices a B hB y hy).read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C):ℝ)

theorem physicalRow_feasible {m : ℕ} (a : Alphabet) (B : ℚ) (hB : B≤1) (y : Allocation m) (hy : Blotto.Feasible (B:ℝ) y)
    (q qbar : ℕ) (hm : 0<m) (hq : 0<q) (hCap : q≤qbar) (hDen : B.den∣q) :
    Blotto.Feasible (B:ℝ) (physicalRow a B hB y hy qbar) :=
  GeneralPaperCodeMixturePhysical.allocation_feasible a true B (response a B hB y hy) q qbar hm hq hCap hDen ⟨0,by change 0<1; decide⟩

theorem share_decoded {m : ℕ} (a : Alphabet) (B : ℚ) (hB : B≤1) (y : Allocation m) (hy : Blotto.Feasible (B:ℝ) y)
    (qbar : ℕ) (hm : 0<m) (hQ : 0<qbar) (j : Fin m) (code : ℕ) (candidate : Choice)
    (hd : (GeneralPaperCodeDecode.decode a false code).choice=some candidate) :
    share (y j) (candidate.physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C):ℝ)=
      share (physicalRow a B hB y hy qbar j) (candidate.physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C):ℝ) := by
  have hv := GeneralPaperCodeDecodeSound.decode_valid a false code candidate hd
  have hb : code<2^a.lambda := by rw [← a.dyadic]; exact valid_in_alphabet a false code hv
  let i : GeneralPaperClosedAlphabet.Closed a := ⟨⟨code,hb⟩,hv⟩
  have hc : GeneralPaperClosedAlphabet.choice a i=candidate :=
    Option.some.inj ((GeneralPaperClosedAlphabet.decoded a i).symm.trans hd)
  have he := GeneralPaperContinuousResponseRow.share_exact a B hB y hy qbar hm hQ j i
  have hvalue : GeneralPaperClosedAlphabet.value a i=candidate.threshold.value := congrArg (fun c : Choice => c.threshold.value) hc
  have hClosed := GeneralPaperCodeDecodeSound.candidate_closed a code candidate hd
  have hPhysical : candidate.physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C)=candidate.threshold.value := by
    simp only [Choice.physical,hClosed,Bool.false_eq_true,ite_false,add_zero]
  rw [hvalue] at he
  rw [hPhysical]
  exact he

theorem payoff_exact {m : ℕ} (a : Alphabet) (BX B : ℚ) (hB : B≤1) (y : Allocation m) (hy : Blotto.Feasible (B:ℝ) y)
    (X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a false BX) (qbar : ℕ) (hm : 0<m) (hQ : 0<qbar)
    (v : Values m) (l : Fin X.law.labels) :
    payoff v y (GeneralPaperCodeMixturePhysical.allocation X qbar l)=
      payoff v (physicalRow a B hB y hy qbar) (GeneralPaperCodeMixturePhysical.allocation X qbar l) := by
  unfold payoff
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun value => v.weight j*value) (share_decoded a B hB y hy qbar hm hQ j _ _ (X.decoded l j))

end Blotto.GeneralPaperContinuousResponseMixture
