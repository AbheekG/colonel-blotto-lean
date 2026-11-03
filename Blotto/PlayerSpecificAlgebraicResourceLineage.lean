import Blotto.PlayerSpecificAlgebraicResourceShape

/-! Ghost certificates for every reached active resource. Original mean
leaves and frozen endpoint leaves remain nonrepeating and disjoint among
active owners. The executing state stores neither these lists nor proofs. -/
namespace Blotto.PlayerSpecificAlgebraicResourceLineage
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
open PlayerSpecificInitialLineageBound PlayerSpecificSignedLineage
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Certificate {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (player : Bool) (s : State N) where
  positive : Fin N → List (Fin N)
  negative : Fin N → List (Fin N)
  positive_valid : PlayerSpecificLineageFamily.Valid s.active positive
  negative_valid : PlayerSpecificLineageFamily.Valid s.active negative
  frozen : ∀ k∈s.active,∀ a∈negative k,a∉s.active
  represents : ∀ k∈s.active,Represents (means p player) (endpoints p) (s.data.read k) (positive k) (negative k)

def start_certificate {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (player : Bool) : Certificate p player (start model p player) where
  positive := fun k => [k]
  negative := fun _ => []
  positive_valid := PlayerSpecificLineageFamily.singleton_valid N _
  negative_valid := PlayerSpecificLineageFamily.empty_valid N _
  frozen := by intro k _ a ha; exact False.elim (List.not_mem_nil ha)
  represents := by
    intro k _
    rw [start_read]
    simp only [Represents,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,sub_zero]

theorem combined_representation {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (player : Bool)
    (s : State N) (i j : Fin N) (extra : Option (Fin N)) (c : Certificate p player s)
    (hi : i∈s.active) (hj : j∈s.active)
    (hm : Normalized p.parameters.root.polynomial) (hm0 : p.parameters.root.polynomial≠[])
    (hs : ∀ k,Reduced p.parameters.root.polynomial (s.data.read k))
    (hL : ∀ k,Reduced p.parameters.root.polynomial (p.rows.read k).length) :
    Represents (means p player) (endpoints p) (PlayerSpecificAlgebraicResourceShape.combined p s i j extra)
      (c.positive i++c.positive j) (c.negative i++c.negative j++extra.toList) := by
  cases extra with
  | none =>
      simpa only [PlayerSpecificAlgebraicResourceShape.combined,Option.toList_none,List.append_nil] using
        PlayerSpecificAlgebraicPairLineage.sum_representation p.parameters.root.polynomial (means p player) (endpoints p)
          _ _ _ _ _ _ hm hm0 (hs i) (hs j) (c.represents i hi) (c.represents j hj)
  | some k =>
      exact PlayerSpecificSignedLineage.merge p.parameters.root.polynomial (means p player) (endpoints p)
        _ _ _ _ _ _ k hm hm0 (hs i) (hs j) (hL k) (c.represents i hi) (c.represents j hj)

theorem advance_certificate {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (player : Bool) (s : State N) (f : Frame N) (hf : request model p s=some f) (upper : Bool)
    (x : ℝ) (hc : PlayerSpecificAlgebraicResourceLoop.Context p x) (hs : Valid p x s)
    (hn : Valid p x (advance model p s f upper)) (c : Certificate p player s) :
    Nonempty (Certificate p player (advance model p s f upper)) := by
  let next:=advance model p s f upper
  have hij:=distinct model p s f hf x hs
  have he:=(fields model p s f hf).1
  have hi : f.first∈s.active := he ▸ List.mem_cons_self
  have hj : f.second∈s.active := he ▸ List.mem_cons_of_mem _ List.mem_cons_self
  have hsub : ∀ k∈next.active,k∈s.active := (PlayerSpecificAlgebraicResourceInvariant.active_sublist model p s f hf upper).subset
  obtain ⟨dropped,extra,hd,hextra,hfrozen,hrow⟩:=PlayerSpecificAlgebraicResourceShape.branch_shape model p s f hf upper hij
  have hdrop : dropped∉next.active := PlayerSpecificAlgebraicResourceShape.frozen_inactive p x next hn dropped hfrozen
  have hdold : dropped∈s.active := by rcases hd with rfl|rfl; exact hi; exact hj
  have hOne : ∀ k∈next.active,∀ l∈next.active,(k=f.first ∨ k=f.second) → (l=f.first ∨ l=f.second) → k=l := by
    intro k hk l hl hkS hlS
    rcases hd with rfl|rfl <;> rcases hkS with rfl|rfl <;> rcases hlS with rfl|rfl <;>
      first | rfl | exact False.elim (hdrop hk) | exact False.elim (hdrop hl)
  have hExtraOld : ∀ a∈extra.toList,a∈s.active := by
    rcases hextra with rfl|rfl
    · simp only [Option.toList_none,List.not_mem_nil,false_implies,implies_true]
    · intro a ha
      have hae : a=dropped := by simpa only [Option.toList_some,List.mem_singleton] using ha
      exact hae ▸ hdold
  have hExtraNew : ∀ a∈extra.toList,a∉next.active := by
    rcases hextra with rfl|rfl
    · simp only [Option.toList_none,List.not_mem_nil,false_implies,implies_true]
    · intro a ha
      have hae : a=dropped := by simpa only [Option.toList_some,List.mem_singleton] using ha
      exact hae ▸ hdrop
  have hp:=PlayerSpecificLineageFamily.merge_valid s.active next.active c.positive f.first f.second []
    c.positive_valid hi hj hij hsub hOne List.nodup_nil (by intro k _ a ha; exact False.elim (List.not_mem_nil ha))
  have hq:=PlayerSpecificLineageFamily.merge_valid s.active next.active c.negative f.first f.second extra.toList
    c.negative_valid hi hj hij hsub hOne (by cases extra <;> simp) (by
      intro k hk a ha hak
      exact c.frozen k hk a hak (hExtraOld a ha))
  have hm0 : p.parameters.root.polynomial≠[] := by intro hz; exact hc.irreducible.ne_zero (by rw [hz]; rfl)
  have hrep:=combined_representation p player s f.first f.second extra c hi hj hc.normalized hm0 hs.reduced hc.lengths
  refine ⟨⟨PlayerSpecificLineageFamily.merge c.positive f.first f.second [],
    PlayerSpecificLineageFamily.merge c.negative f.first f.second extra.toList,hp,hq,?_,?_⟩⟩
  · intro k hk a ha hactive
    by_cases hks : k=f.first ∨ k=f.second
    · simp only [PlayerSpecificLineageFamily.merge,ite_eq_left hks,List.mem_append] at ha
      rcases ha with (hai|haj)|haf
      · exact c.frozen f.first hi a hai (hsub a hactive)
      · exact c.frozen f.second hj a haj (hsub a hactive)
      · exact hExtraNew a haf hactive
    · simp only [PlayerSpecificLineageFamily.merge,ite_eq_right hks] at ha
      exact c.frozen k (hsub k hk) a ha (hsub a hactive)
  · intro k hk
    by_cases hks : k=f.first ∨ k=f.second
    · simp only [PlayerSpecificLineageFamily.merge,ite_eq_left hks,List.append_nil]
      rw [hrow k hks (by intro h; exact hdrop (h ▸ hk))]
      exact hrep
    · simp only [PlayerSpecificLineageFamily.merge,ite_eq_right hks]
      rw [PlayerSpecificAlgebraicResourceShape.read_other model p s f upper k
        (fun e => hks (Or.inl e)) (fun e => hks (Or.inr e))]
      exact c.represents k (hsub k hk)

end Blotto.PlayerSpecificAlgebraicResourceLineage
