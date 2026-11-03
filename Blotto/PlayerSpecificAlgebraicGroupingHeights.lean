import Blotto.PlayerSpecificAlgebraicGroupingShape

/-! Additive coefficient growth along the executed greedy loop. The
potential charges one original endpoint per remaining item. -/
namespace Blotto.PlayerSpecificAlgebraicGroupingHeights
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicGrouping
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem aux {N : ℕ} (model : RationalCostModel) (root : Candidate) (lengths : FixedArrayTable N Data) (B : ℚ)
    (T S : ℕ) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hl : ∀ k,Reduced root.polynomial (lengths.read k) ∧ HasHeight (lengths.read k) T)
    (rest : List (Fin N)) : ∀ (current : List (Fin N)) (s : Data) (C : ℕ),
    Reduced root.polynomial s → HasHeight s C → C+(rest.length+1)*(T+1)≤S →
    ∀ g∈(PlayerSpecificAlgebraicGroupingExecution.packAux model root lengths B current s rest).1,
      Reduced root.polynomial g.total ∧ HasHeight g.total S := by
  intro current s C hs hsC hpotential
  rw [PlayerSpecificAlgebraicGroupingExecution.aux_value]
  induction rest generalizing current s C with
  | nil =>
    intro g hg
    have hg' : g=⟨current.reverse,s⟩ := by simpa only [PlayerSpecificAlgebraicGrouping.packAux,List.mem_singleton] using hg
    subst g
    exact ⟨hs,mono hsC (by omega)⟩
  | cons k rest ih =>
    have hsum:=PlayerSpecificAlgebraicField.plus_reduced root.polynomial s (lengths.read k) hm hm0
    have hsumH:=PlayerSpecificShortReduction.plus_height root.polynomial s (lengths.read k) hm hm0 hs (hl k).1 C T hsC (hl k).2
    simp only [List.length_cons] at hpotential
    have hnext : C+T+1+(rest.length+1)*(T+1)≤S := by nlinarith only [hpotential]
    have hreset : T+(rest.length+1)*(T+1)≤S := by nlinarith only [hpotential,Nat.zero_le C]
    unfold PlayerSpecificAlgebraicGrouping.packAux
    dsimp only
    split
    · exact ih (k::current) _ (C+T+1) hsum hsumH hnext
    · intro g hg
      rcases List.mem_cons.mp hg with rfl|hg
      · exact ⟨hs,mono hsC (by omega)⟩
      · exact ih [k] (lengths.read k) T (hl k).1 (hl k).2 hreset g hg

theorem run {N : ℕ} (model : RationalCostModel) (root : Candidate) (lengths : FixedArrayTable N Data) (B : ℚ)
    (items : List (Fin N)) (T S : ℕ) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hl : ∀ k,Reduced root.polynomial (lengths.read k) ∧ HasHeight (lengths.read k) T)
    (hpotential : (items.length+1)*(T+1)≤S) :
    ∀ g∈(PlayerSpecificAlgebraicGroupingExecution.run model root lengths B items).1,
      Reduced root.polynomial g.total ∧ HasHeight g.total S := by
  cases items with
  | nil => intro g hg; exact False.elim (List.not_mem_nil hg)
  | cons k rest =>
    exact aux model root lengths B T S hm hm0 hl rest [k] (lengths.read k) T (hl k).1 (hl k).2
      (by simp only [List.length_cons] at hpotential; nlinarith only [hpotential])

end Blotto.PlayerSpecificAlgebraicGroupingHeights
