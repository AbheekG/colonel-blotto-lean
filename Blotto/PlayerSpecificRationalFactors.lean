import Blotto.PlayerSpecificLinearFactor

/-! Executable removal of every rational linear factor, including repeated
factors. Each step enumerates actual rational roots and divides by one recovered
linear factor. Stored-length descent makes four steps sufficient for cubics. -/
namespace Blotto.PlayerSpecificRationalFactors
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization
open PlayerSpecificLinearFactor
set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable def product : Data → Polynomial ℚ
  | [] => 1
  | q::qs => semantics (linear q)*product qs

def run : ℕ → Data → Data×Data
  | 0,p => ([],trim p)
  | fuel+1,p =>
    match PlayerSpecificRationalRoots.run p with
    | [] => ([],trim p)
    | q::_ =>
      let rest:=run fuel (quotient p q)
      (q::rest.1,rest.2)

theorem contract (fuel : ℕ) (p : Data) (hp : semantics p≠0)
    (hlen : p.length≤4) (hfuel : p.length≤fuel) :
    Normalized (run fuel p).2 ∧ semantics (run fuel p).2≠0 ∧
      (∀ x : ℚ,evaluate (run fuel p).2 x≠0) ∧
      semantics p=product (run fuel p).1*semantics (run fuel p).2 ∧
      (run fuel p).2.length≤p.length ∧
      (run fuel p).1.length+(semantics (run fuel p).2).natDegree=(semantics p).natDegree ∧
      (∀ q ∈ (run fuel p).1,evaluate p q=0) := by
  induction fuel generalizing p with
  | zero =>
    have hz : p=[] := List.length_eq_zero_iff.mp (by omega)
    exact (hp (by rw [hz]; rfl)).elim
  | succ fuel ih =>
    cases hroots : PlayerSpecificRationalRoots.run p with
    | nil =>
      have hn : ∀ x : ℚ,evaluate p x≠0 := by
        intro x hx
        have hm: x∈PlayerSpecificRationalRoots.run p :=
          (PlayerSpecificRationalRoots.mem_iff p hp hlen x).mpr hx
        rw [hroots] at hm
        exact List.not_mem_nil hm
      simp only [run,hroots]
      refine ⟨trim_normalized p,?_,?_,?_,trim_length p,?_,?_⟩
      · rwa [trim_semantics]
      · intro x
        simpa only [←evaluate_semantics,trim_semantics] using hn x
      · simp only [product,one_mul,trim_semantics]
      · simp only [List.length_nil,zero_add,trim_semantics]
      · simp only [List.not_mem_nil,false_implies,implies_true]
    | cons q qs =>
      have hq : evaluate p q=0 := PlayerSpecificRationalRoots.sound p q (by rw [hroots]; exact List.mem_cons_self)
      have hd:=length_drop p hp q hq
      have hnonzero:=quotient_nonzero p hp q hq
      have hrest:=ih (quotient p q) hnonzero (by omega) (by omega)
      simp only [run,hroots]
      refine ⟨hrest.1,hrest.2.1,hrest.2.2.1,?_,?_,?_,?_⟩
      · calc
          semantics p=semantics (linear q)*semantics (quotient p q) := decomposition p q hq
          _=product (q::(run fuel (quotient p q)).1)*semantics (run fuel (quotient p q)).2 := by
            rw [hrest.2.2.2.1]
            exact (mul_assoc _ _ _).symm
      · exact hrest.2.2.2.2.1.trans (by omega)
      · have hdegree:=degree_drop p hp q hq
        have hi:=hrest.2.2.2.2.2.1
        simp only [List.length_cons]
        omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | htail
        · exact hq
        · exact quotient_root_subset p q x hq (hrest.2.2.2.2.2.2 x htail)

def factor (p : Data) : Data×Data := run p.length p

theorem factor_contract (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    Normalized (factor p).2 ∧ semantics (factor p).2≠0 ∧
      (∀ x : ℚ,evaluate (factor p).2 x≠0) ∧
      semantics p=product (factor p).1*semantics (factor p).2 ∧
      (factor p).2.length≤p.length ∧
      (factor p).1.length+(semantics (factor p).2).natDegree=(semantics p).natDegree ∧
      (∀ q ∈ (factor p).1,evaluate p q=0) := contract p.length p hp hlen (le_refl _)

theorem residual_irreducible (p : Data) (hp : semantics p≠0) (hlen : p.length≤4)
    (hpositive : 0<(semantics (factor p).2).natDegree) : Irreducible (semantics (factor p).2) := by
  have hc:=factor_contract p hp hlen
  have hd:=degree_le (factor p).2
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp only [Finset.mem_Icc]
    omega
  · intro x hx
    exact hc.2.2.1 x (by simpa only [Polynomial.IsRoot,evaluate_semantics] using hx)

end Blotto.PlayerSpecificRationalFactors
