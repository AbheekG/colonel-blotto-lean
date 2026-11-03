import Blotto.PlayerSpecificAlgebraicLeafAssignments

/-! Direct original-leaf writes agree exactly with proportional splitting.
Copying the fractional coordinate is valid because it belongs to no group. -/
namespace Blotto.PlayerSpecificAlgebraicLeafValues
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicGrouping PlayerSpecificAlgebraicGroupingCache PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicLeafAssignments PlayerSpecificAlgebraicLeafPartition
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def point {N m : ℕ} (G : ProportionalGroups N m) (fractional : Option (Fin N))
    (y : Allocation 4) : Allocation N := fun j => G.split (fun g => y (slot g)) j+
      match fractional with | none => 0 | some k => if j=k then y 3 else 0

theorem value {N : ℕ} (root : Candidate) (length : Fin N → Data) (groups : List (Group N)) (x : ℝ)
    (hL : ∀ j,0 < realEvaluate (length j) x) (hn : (groups.map Group.members).flatten.Nodup)
    (hcache : ∀ g ∈ groups,Cache root length g) (hpos : ∀ g ∈ groups,0 < realEvaluate g.total x)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hx : realEvaluate root.polynomial x=0) (y : FixedArrayTable 4 Data) :
    PlayerSpecificAlgebraicSegment.values (emit root length groups y) x=
      (partition root length groups x hL hn hcache hpos).split
        (fun g => realEvaluate (y.read (slot g)) x) := by
  let G := partition root length groups x hL hn hcache hpos
  funext j
  change realEvaluate ((emit root length groups y).read j) x=G.split _ j
  by_cases he : ∃ g : Fin groups.length,j ∈ (groups.get g).members
  · obtain ⟨g,hg⟩ := he
    have hjG : j ∈ G.members g := (mem_partition root length groups x hL hn hcache hpos g j).mpr hg
    rw [emit_group root length groups y hn g j hg,G.split_group_coordinate hjG,
      total_value root length groups x hL hn hcache hpos g,
      PlayerSpecificAlgebraicField.times_value _ _ _ x hx,
      PlayerSpecificAlgebraicField.divide_value root.polynomial (length j) (groups.get g).total hm hirr
        (hcache _ (List.get_mem groups g)).1 x hx]
    rfl
  · have hj : ∀ g : Fin groups.length,j ∉ (groups.get g).members := by
      intro g hg; exact he ⟨g,hg⟩
    have hjG : ∀ g,j ∉ G.members g := by
      intro g hg
      exact hj g ((mem_partition root length groups x hL hn hcache hpos g j).mp hg)
    rw [emit_inactive root length groups y j hj,G.split_inactive_coordinate hjG]
    rfl

theorem mixed_value {N : ℕ} (root : Candidate) (length : Fin N → Data) (groups : List (Group N)) (x : ℝ)
    (hL : ∀ j,0 < realEvaluate (length j) x) (hn : (groups.map Group.members).flatten.Nodup)
    (hcache : ∀ g ∈ groups,Cache root length g) (hpos : ∀ g ∈ groups,0 < realEvaluate g.total x)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hx : realEvaluate root.polynomial x=0) (fractional : Option (Fin N))
    (hp : ∀ k,fractional=some k → ∀ g : Fin groups.length,k ∉ (groups.get g).members)
    (y : FixedArrayTable 4 Data) :
    PlayerSpecificAlgebraicSegment.values (emitMixed root length groups fractional y) x=
      point (partition root length groups x hL hn hcache hpos) fractional (PlayerSpecificAlgebraicSegment.values y x) := by
  let G := partition root length groups x hL hn hcache hpos
  have hv := value root length groups x hL hn hcache hpos hm hirr hx y
  cases fractional with
  | none =>
    funext j
    change realEvaluate ((emit root length groups y).read j) x=
      G.split (fun g => realEvaluate (y.read (slot g)) x) j+0
    rw [add_zero]
    exact congrFun hv j
  | some k =>
    have hk : ∀ g,k ∉ G.members g := by
      intro g hg
      exact hp k rfl g ((mem_partition root length groups x hL hn hcache hpos g k).mp hg)
    funext j
    change realEvaluate ((emitMixed root length groups (some k) y).read j) x=
      G.split (fun g => realEvaluate (y.read (slot g)) x) j+if j=k then realEvaluate (y.read 3) x else 0
    by_cases hj : j=k
    · subst j
      rw [emitMixed_pivot,G.split_inactive_coordinate hk]
      simp
    · rw [emitMixed_other root length groups y k j hj,ite_eq_right hj,add_zero]
      exact congrFun hv j

end Blotto.PlayerSpecificAlgebraicLeafValues
