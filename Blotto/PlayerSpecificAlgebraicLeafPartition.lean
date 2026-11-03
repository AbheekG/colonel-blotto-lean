import Blotto.PlayerSpecificAlgebraicTerminalCoreExecution

/-! The actual cached member lists induce a proof-only proportional
partition. Its totals are precisely the computed algebraic group totals;
no partition is provided to the runtime leaf allocator. -/
namespace Blotto.PlayerSpecificAlgebraicLeafPartition
open PlayerSpecificDensePolynomial PlayerSpecificSturmVariations PlayerSpecificAlgebraicGrouping
open PlayerSpecificAlgebraicGroupingCache PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem members_nodup {N : ℕ} (groups : List (Group N))
    (hn : (groups.map Group.members).flatten.Nodup) (g : Fin groups.length) : (groups.get g).members.Nodup :=
  (List.nodup_flatten.mp hn).1 _ (List.mem_map.mpr ⟨groups.get g,List.get_mem groups g,rfl⟩)

theorem indices_unique {N : ℕ} (groups : List (Group N))
    (hn : (groups.map Group.members).flatten.Nodup) (g h : Fin groups.length) (j : Fin N)
    (hg : j ∈ (groups.get g).members) (hh : j ∈ (groups.get h).members) : g=h := by
  have hp : groups.Pairwise (fun a b => List.Disjoint a.members b.members) := by
    simpa only [List.pairwise_map] using (List.nodup_flatten.mp hn).2
  have hi := List.pairwise_iff_get.mp hp
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt|hlt
  · exact List.disjoint_left.mp (hi g h hlt) hg hh
  · exact List.disjoint_left.mp (hi h g hlt) hh hg

noncomputable def partition {N : ℕ} (root : Candidate) (length : Fin N → Data) (groups : List (Group N)) (x : ℝ)
    (hL : ∀ j,0 < realEvaluate (length j) x) (hn : (groups.map Group.members).flatten.Nodup)
    (hcache : ∀ g ∈ groups,Cache root length g) (hpos : ∀ g ∈ groups,0 < realEvaluate g.total x) :
    ProportionalGroups N groups.length where
  length := fun j => realEvaluate (length j) x
  length_pos := hL
  members := fun g => (groups.get g).members.toFinset
  disjoint := by
    intro g h hgh
    apply Finset.disjoint_left.mpr
    intro j hj hk
    exact hgh (indices_unique groups hn g h j (by simpa using hj) (by simpa using hk))
  total_pos := by
    intro g
    rw [List.sum_toFinset _ (members_nodup groups hn g)]
    change 0 < groupLength (fun j => realEvaluate (length j) x) (groups.get g).members
    rw [← cache_value root length (groups.get g) (hcache _ (List.get_mem groups g)) x]
    exact hpos _ (List.get_mem groups g)

theorem mem_partition {N : ℕ} (root : Candidate) (length : Fin N → Data) (groups : List (Group N)) (x : ℝ)
    (hL : ∀ j,0 < realEvaluate (length j) x) (hn : (groups.map Group.members).flatten.Nodup)
    (hcache : ∀ g ∈ groups,Cache root length g) (hpos : ∀ g ∈ groups,0 < realEvaluate g.total x)
    (g : Fin groups.length) (j : Fin N) :
    j ∈ (partition root length groups x hL hn hcache hpos).members g ↔ j ∈ (groups.get g).members := by
  change j ∈ (groups.get g).members.toFinset ↔ _
  exact List.mem_toFinset

theorem total_value {N : ℕ} (root : Candidate) (length : Fin N → Data) (groups : List (Group N)) (x : ℝ)
    (hL : ∀ j,0 < realEvaluate (length j) x) (hn : (groups.map Group.members).flatten.Nodup)
    (hcache : ∀ g ∈ groups,Cache root length g) (hpos : ∀ g ∈ groups,0 < realEvaluate g.total x)
    (g : Fin groups.length) :
    (partition root length groups x hL hn hcache hpos).total g=realEvaluate (groups.get g).total x := by
  change (∑ j ∈ (groups.get g).members.toFinset,realEvaluate (length j) x)=_
  rw [List.sum_toFinset _ (members_nodup groups hn g)]
  exact (cache_value root length (groups.get g) (hcache _ (List.get_mem groups g)) x).symm

end Blotto.PlayerSpecificAlgebraicLeafPartition
