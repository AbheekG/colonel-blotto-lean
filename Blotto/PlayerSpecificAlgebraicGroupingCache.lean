import Blotto.PlayerSpecificAlgebraicGrouping

/-! Cached group totals are literal reduced sums of original endpoint
rows. Their sizes are bounded by nonrepeating leaves. -/
namespace Blotto.PlayerSpecificAlgebraicGroupingCache
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicGrouping
set_option autoImplicit false
set_option maxHeartbeats 2500000

def Cache {N : ℕ} (root : Candidate) (length : Fin N → Data) (g : Group N) : Prop :=
  Reduced root.polynomial g.total ∧ semantics g.total=((g.members.map length).map semantics).sum

theorem aux_cache {N : ℕ} (model : RationalCostModel) (root : Candidate) (length : Fin N → Data) (B : ℚ)
    (current : List (Fin N)) (s : Data) (rest : List (Fin N))
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hL : ∀ k,Reduced root.polynomial (length k)) (hs : Reduced root.polynomial s)
    (hrep : semantics s=((current.map length).map semantics).sum) :
    ∀ g∈PlayerSpecificAlgebraicGrouping.packAux model root length B current s rest,Cache root length g := by
  induction rest generalizing current s with
  | nil =>
      intro g hg
      have hg' : g=⟨current.reverse,s⟩ := by simpa only [PlayerSpecificAlgebraicGrouping.packAux,List.mem_singleton] using hg
      subst g
      exact ⟨hs,by simpa only [List.map_reverse,List.sum_reverse] using hrep⟩
  | cons k rest ih =>
      have hsum:=PlayerSpecificAlgebraicField.plus_reduced root.polynomial s (length k) hm hm0
      have hnew : semantics (PlayerSpecificAlgebraicField.plus root.polynomial s (length k))=
          (((k::current).map length).map semantics).sum := by
        rw [PlayerSpecificAdditiveFieldSemantics.plus _ _ _ hm hm0 hs (hL k),hrep]
        simp only [List.map_cons,List.sum_cons]
        ring
      unfold PlayerSpecificAlgebraicGrouping.packAux
      dsimp only
      split
      · exact ih _ _ hsum hnew
      · intro g hg
        rcases List.mem_cons.mp hg with rfl|hg
        · exact ⟨hs,by simpa only [List.map_reverse,List.sum_reverse] using hrep⟩
        · exact ih [k] (length k) (hL k) (by simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]) g hg

theorem cache {N : ℕ} (model : RationalCostModel) (root : Candidate) (length : Fin N → Data) (B : ℚ)
    (items : List (Fin N)) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hL : ∀ k,Reduced root.polynomial (length k)) : ∀ g∈run model root length B items,Cache root length g := by
  cases items with
  | nil => intro g hg; exact False.elim (List.not_mem_nil hg)
  | cons k rest =>
      exact aux_cache model root length B [k] (length k) rest hm hm0 hL (hL k)
        (by simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero])

theorem cache_value {N : ℕ} (root : Candidate) (length : Fin N → Data) (g : Group N)
    (hc : Cache root length g) (x : ℝ) : realEvaluate g.total x=groupLength (fun k => realEvaluate (length k) x) g.members := by
  have h:=congrArg (fun p : Polynomial ℚ => p.eval₂ (Rat.castHom ℝ) x) hc.2
  rw [realEvaluate_semantics] at h
  simpa only [groupLength,Polynomial.eval₂_list_sum,List.map_map,Function.comp_def,realEvaluate_semantics] using h

theorem cache_height {N : ℕ} (root : Candidate) (length : Fin N → Data) (g : Group N)
    (hc : Cache root length g) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (H : ℕ) (hL : ∀ k,Reduced root.polynomial (length k) ∧ HasHeight (length k) H)
    (hn : g.members.Nodup) : HasHeight g.total ((H+1)*(N+N)+3) := by
  apply PlayerSpecificSignedLineage.representation_height root.polynomial length length g.total g.members []
    hm hm0 hc.1 H hL hL hn List.nodup_nil
  simpa only [PlayerSpecificSignedLineage.Represents,List.map_nil,List.sum_nil,sub_zero] using hc.2

end Blotto.PlayerSpecificAlgebraicGroupingCache
