import Blotto.PlayerSpecificSturmLocalCounts

/-! Executable exact distinct-real-root counts on rational intervals. All
numerical work uses the computed rational squarefree/Sturm sequence. The
noncomputable root set is used only to state/prove correctness, never by
the executable counter. Intervals use (a,b], including rational roots at b. -/
namespace Blotto.PlayerSpecificSturmRootCount
open PlayerSpecificDensePolynomial PlayerSpecificSturmVariations PlayerSpecificSquarefreeAlgorithm
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable def roots (p : Data) : Finset ℝ := (realPolynomial p).roots.toFinset

theorem mem_roots (p : Data) (hp : semantics p≠0) (x : ℝ) :
    x∈roots p ↔ realEvaluate p x=0 := by
  simp only [roots,Multiset.mem_toFinset,Polynomial.mem_roots (real_nonzero p hp),Polynomial.IsRoot,real_evaluate]

def rows (p : Data) : List Data := PlayerSpecificSturmSequence.run (PlayerSpecificSquarefreeAlgorithm.run p)

def count (p : Data) (a b : ℚ) : ℕ :=
  PlayerSpecificSturmSequence.variations (rows p) a-PlayerSpecificSturmSequence.variations (rows p) b

noncomputable def variation (p : Data) (x : ℝ) : ℕ :=
  PlayerSpecificSturmLocalCounts.value (PlayerSpecificSquarefreeAlgorithm.run p) x

theorem squarefree_nonzero (p : Data) (hp : semantics p≠0) : semantics (PlayerSpecificSquarefreeAlgorithm.run p)≠0 :=
  PlayerSpecificSquarefreeReduction.quotient_nonzero _ _ _ hp (decomposition p)

theorem away (p : Data) (hp : semantics p≠0) : PlayerSpecificFiniteJumpCount.Away (roots p) (variation p) := by
  intro a ha
  apply PlayerSpecificSturmLocalCounts.away (PlayerSpecificSquarefreeAlgorithm.run p) (squarefree_nonzero p hp)
    (real_simple_roots p hp) a
  intro hz
  apply ha
  exact (mem_roots p hp a).mpr ((evaluated_roots_preserved p hp a).mp hz)

theorem jumps (p : Data) (hp : semantics p≠0) : PlayerSpecificFiniteJumpCount.Jumps (roots p) (variation p) := by
  intro a ha
  apply PlayerSpecificSturmLocalCounts.jumps (PlayerSpecificSquarefreeAlgorithm.run p) (squarefree_nonzero p hp)
    (real_simple_roots p hp) a
  exact (evaluated_roots_preserved p hp a).mpr ((mem_roots p hp a).mp ha)

theorem endpoint_value (p : Data) (x : ℚ) :
    variation p (x : ℝ)=PlayerSpecificSturmSequence.variations (rows p) x :=
  endpoint_variations (rows p) x

theorem exact_count (p : Data) (hp : semantics p≠0) (a b : ℚ) (hab : a≤b) :
    count p a b=(roots p |>.filter (fun r => (a : ℝ)<r ∧ r≤(b : ℝ))).card := by
  have h := PlayerSpecificFiniteJumpCount.interval_count_sub (roots p) (variation p) (away p hp) (jumps p hp)
    (a : ℝ) (b : ℝ) (by exact_mod_cast hab)
  rw [endpoint_value,endpoint_value] at h
  exact h

theorem variations_antitone (p : Data) (hp : semantics p≠0) (a b : ℚ) (hab : a≤b) :
    PlayerSpecificSturmSequence.variations (rows p) b≤PlayerSpecificSturmSequence.variations (rows p) a := by
  have h := PlayerSpecificFiniteJumpCount.interval_count (roots p) (variation p) (away p hp) (jumps p hp)
    (a : ℝ) (b : ℝ) (by exact_mod_cast hab)
  rw [endpoint_value,endpoint_value] at h
  omega

theorem positive_iff (p : Data) (hp : semantics p≠0) (a b : ℚ) (hab : a≤b) :
    0<count p a b ↔ ∃ r : ℝ,realEvaluate p r=0 ∧ (a : ℝ)<r ∧ r≤(b : ℝ) := by
  rw [exact_count p hp a b hab]
  constructor
  · intro h
    rcases Finset.card_pos.mp h with ⟨r,hr⟩
    have hd := Finset.mem_filter.mp hr
    exact ⟨r,(mem_roots p hp r).mp hd.1,hd.2⟩
  · rintro ⟨r,hr,ha,hb⟩
    exact Finset.card_pos.mpr ⟨r,Finset.mem_filter.mpr ⟨(mem_roots p hp r).mpr hr,ha,hb⟩⟩

theorem zero_iff (p : Data) (hp : semantics p≠0) (a b : ℚ) (hab : a≤b) :
    count p a b=0 ↔ ¬∃ r : ℝ,realEvaluate p r=0 ∧ (a : ℝ)<r ∧ r≤(b : ℝ) := by
  constructor
  · intro hz hr
    have h := (positive_iff p hp a b hab).mpr hr
    omega
  · intro hn
    by_contra hne
    exact hn ((positive_iff p hp a b hab).mp (Nat.pos_of_ne_zero hne))

theorem additive (p : Data) (hp : semantics p≠0) (a b c : ℚ) (hab : a≤b) (hbc : b≤c) :
    count p a c=count p a b+count p b c := by
  have h1 := variations_antitone p hp a b hab
  have h2 := variations_antitone p hp b c hbc
  unfold count
  omega

theorem one_unique (p : Data) (hp : semantics p≠0) (a b : ℚ) (hab : a≤b) (hcount : count p a b=1) :
    ∃! r : ℝ,realEvaluate p r=0 ∧ (a : ℝ)<r ∧ r≤(b : ℝ) := by
  have hc : (roots p |>.filter (fun r => (a : ℝ)<r ∧ r≤(b : ℝ))).card=1 := by
    rw [← exact_count p hp a b hab]
    exact hcount
  rcases Finset.card_eq_one.mp hc with ⟨r,hr⟩
  have hm : r∈(roots p).filter (fun r => (a : ℝ)<r ∧ r≤(b : ℝ)) := by rw [hr]; exact Finset.mem_singleton_self _
  have hd := Finset.mem_filter.mp hm
  refine ⟨r,⟨(mem_roots p hp r).mp hd.1,hd.2⟩,?_⟩
  intro s hs
  have hsm : s∈(roots p).filter (fun r => (a : ℝ)<r ∧ r≤(b : ℝ)) :=
    Finset.mem_filter.mpr ⟨(mem_roots p hp s).mpr hs.1,hs.2⟩
  rw [hr,Finset.mem_singleton] at hsm
  exact hsm

end Blotto.PlayerSpecificSturmRootCount
