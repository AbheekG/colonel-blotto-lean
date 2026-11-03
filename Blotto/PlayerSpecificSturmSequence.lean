import Blotto.PlayerSpecificPolynomialGCD
import Mathlib.Data.List.SignVariations

/-! Executable signed Euclidean sequences and rational endpoint variation
counts. The root-counting/isolation theorem is a later obligation; this
module verifies the sequence's actual remainder identities and termination. -/
namespace Blotto.PlayerSpecificSturmSequence
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization
set_option autoImplicit false
set_option maxHeartbeats 3500000

def next (p q : Data) : Data := trim (scale (-1) (PlayerSpecificPolynomialDivision.run p q).2)

theorem next_semantics (p q : Data) :
    semantics (next p q) = -semantics (PlayerSpecificPolynomialDivision.run p q).2 := by
  rw [next,trim_semantics,scale_semantics]
  simp only [map_neg,map_one,neg_one_mul]

theorem next_normalized (p q : Data) : Normalized (next p q) := trim_normalized _

theorem next_length (p q : Data) (hq : Normalized q) (hq0 : q≠[]) : (next p q).length<q.length := by
  have ht := trim_length (scale (-1) (PlayerSpecificPolynomialDivision.run p q).2)
  rw [scale_length] at ht
  exact ht.trans_lt (PlayerSpecificPolynomialDivision.remainder_length p q hq hq0)

theorem next_identity (p q : Data) :
    semantics p=semantics q*semantics (PlayerSpecificPolynomialDivision.run p q).1-semantics (next p q) := by
  rw [next_semantics,sub_neg_eq_add]
  exact (PlayerSpecificPolynomialDivision.reconstruction p q).symm

def chain : ℕ → Data → Data → List Data
  | 0,_,q => if q=[] then [] else [q]
  | fuel+1,p,q => if q=[] then [] else q::chain fuel q (next p q)

theorem head (fuel : ℕ) (p q : Data) : (chain fuel p q).head?=if q=[] then none else some q := by
  cases fuel <;> simp only [chain] <;> split <;> rfl

theorem empty_iff (fuel : ℕ) (p q : Data) : chain fuel p q=[] ↔ q=[] := by
  rw [← List.head?_eq_none_iff,head]
  by_cases hq : q=[] <;> simp only [hq,ite_true,ite_false,Option.some_ne_none]

theorem first (fuel : ℕ) (p q r : Data) (rows : List Data) (h : chain fuel p q=r::rows) : r=q := by
  have hh := head fuel p q
  rw [h] at hh
  by_cases hq : q=[]
  · rw [ite_eq_left hq] at hh
    cases hh
  · rw [ite_eq_right hq] at hh
    exact Option.some.inj hh

theorem length_bound (fuel : ℕ) (p q : Data) (hq : Normalized q) : (chain fuel p q).length≤q.length := by
  induction fuel generalizing p q with
  | zero =>
    rw [chain]
    split
    · simp only [List.length_nil]; omega
    · rename_i hq0
      have hpos := List.length_pos_iff.mpr hq0
      simp only [List.length_singleton]
      omega
  | succ fuel ih =>
    rw [chain]
    split
    · simp only [List.length_nil]; omega
    · rename_i hq0
      have hdrop := next_length p q hq hq0
      have ht := ih q (next p q) (next_normalized p q)
      simp only [List.length_cons]
      omega

def Links (p : Data) : List Data → Prop
  | [] => True
  | q::rows => Normalized q ∧ q≠[] ∧ Links q rows ∧
    match rows with
    | [] => semantics (PlayerSpecificPolynomialDivision.run p q).2=0
    | r::_ => semantics p=semantics q*semantics (PlayerSpecificPolynomialDivision.run p q).1-semantics r

theorem links (fuel : ℕ) (p q : Data) (hq : Normalized q) (hcap : q.length≤fuel) :
    Links p (chain fuel p q) := by
  induction fuel generalizing p q with
  | zero =>
    have hz : q=[] := List.length_eq_zero_iff.mp (by omega)
    simp only [chain,hz,ite_true,Links]
  | succ fuel ih =>
    rw [chain]
    split
    · trivial
    · rename_i hq0
      have hd := next_length p q hq hq0
      have ht := ih q (next p q) (next_normalized p q) (by omega)
      refine ⟨hq,hq0,ht,?_⟩
      cases he : chain fuel q (next p q) with
      | nil =>
        have hn := (empty_iff fuel q (next p q)).mp he
        have hz : semantics (next p q)=0 := by rw [hn]; rfl
        rw [next_semantics,neg_eq_zero] at hz
        exact hz
      | cons r rows =>
        have hr := first fuel q (next p q) r rows he
        rw [hr]
        exact next_identity p q

def run (p : Data) : List Data :=
  let first := trim p
  let second := trim (derivative first)
  if first=[] then [] else first::chain second.length first second

def variations (rows : List Data) (x : ℚ) : ℕ := (rows.map (fun p => evaluate p x)).signVariations

theorem run_length (p : Data) : (run p).length≤p.length+1 := by
  have h := length_bound (trim (derivative (trim p))).length (trim p) (trim (derivative (trim p))) (trim_normalized _)
  have h1 := trim_length (derivative (trim p))
  have h2 := derivative_length (trim p)
  have h3 := trim_length p
  unfold run
  dsimp only
  split <;> simp only [List.length_nil,List.length_cons] <;> omega

end Blotto.PlayerSpecificSturmSequence
