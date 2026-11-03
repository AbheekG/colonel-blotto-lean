import Blotto.PlayerSpecificAlgebraicResourceRequest

/-! Exact active-list membership and reduced-array invariants survive
the actual selected-entry update. The tail is retained without a scan. -/
namespace Blotto.PlayerSpecificAlgebraicResourceUpdate
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem valid {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N)
    (i j : Fin N) (tail : List (Fin N)) (a b : Data) (he : s.active=i::j::tail)
    (hm : Normalized p.parameters.root.polynomial) (hirr : Irreducible (semantics p.parameters.root.polynomial))
    (hv : p.parameters.root.interval.lo<p.parameters.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique p.parameters.root.polynomial p.parameters.root.interval x)
    (hs : Valid p x s) (ha : Reduced p.parameters.root.polynomial a) (hb : Reduced p.parameters.root.polynomial b) :
    Valid p x (update model p s i j tail a b) := by
  let d:=(s.data.write i a).write j b
  let test:=fun k => PlayerSpecificAlgebraicActive.run model p.parameters.root (p.rows.read k).length (d.read k)
  have htest : ∀ k,test k=true ↔ Fractional (lengths p x) (eval (update model p s i j tail a b) x) k := by
    intro k
    exact PlayerSpecificAlgebraicActive.correct model p.parameters.root _ _ hm hirr hv x hx
  have hn : (i::j::tail).Nodup := he ▸ hs.nodup
  have hnParts:=hn
  rw [List.nodup_cons,List.nodup_cons] at hnParts
  have hiTail : i∉tail := fun h => hnParts.1 (List.mem_cons_of_mem j h)
  have hjTail : j∉tail := hnParts.2.1
  constructor
  · change ([i,j].filter test++tail).Nodup
    have hsub : ([i,j].filter test).Sublist [i,j] := List.filter_sublist
    exact (hsub.append (List.Sublist.refl tail)).nodup hn
  · intro k
    change k∈([i,j].filter test++tail) ↔ Fractional (lengths p x) (eval (update model p s i j tail a b) x) k
    simp only [List.mem_append,List.mem_filter,List.mem_cons,List.not_mem_nil,or_false,htest]
    by_cases hki : k=i
    · subst k
      simp [hiTail]
    · by_cases hkj : k=j
      · subst k
        simp [hjTail]
      · simp only [hki,hkj,false_or,false_and]
        have hold : k∈tail ↔ Fractional (lengths p x) (eval s x) k := by
          simpa only [he,List.mem_cons,hki,hkj,false_or] using hs.membership k
        have hread : d.read k=s.data.read k := by
          simp only [d,FixedArrayTable.read_write,ite_eq_right hkj,ite_eq_right hki]
        have hfrac : Fractional (lengths p x) (eval (update model p s i j tail a b) x) k ↔
            Fractional (lengths p x) (eval s x) k := by
          change (0<realEvaluate (d.read k) x ∧ realEvaluate (d.read k) x<lengths p x k) ↔ _
          simp only [hread]
          rfl
        exact hold.trans hfrac.symm
  · intro k
    change Reduced p.parameters.root.polynomial (((s.data.write i a).write j b).read k)
    rw [FixedArrayTable.read_write,FixedArrayTable.read_write]
    split
    · exact hb
    · split
      · exact ha
      · exact hs.reduced k

end Blotto.PlayerSpecificAlgebraicResourceUpdate
