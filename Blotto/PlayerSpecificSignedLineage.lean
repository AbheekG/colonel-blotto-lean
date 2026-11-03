import Blotto.PlayerSpecificAdditiveFieldSemantics

/-! A signed lineage certificate bounds actual stored reduced rows by
their original leaves, independently of the order of pairwise updates.
The certificate is a proof invariant; a sampler need not store lineage
lists at runtime. No global sampler invariant is asserted here. -/
namespace Blotto.PlayerSpecificSignedLineage
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 2500000

def sumRows (m : Data) : List Data → Data
  | [] => []
  | a::rows => PlayerSpecificAlgebraicField.plus m a (sumRows m rows)

theorem sum_reduced (m : Data) (rows : List Data) (hm : Normalized m) (hm0 : m≠[]) : Reduced m (sumRows m rows) := by
  cases rows
  · exact nil_reduced m hm0
  · exact PlayerSpecificAlgebraicField.plus_reduced _ _ _ hm hm0

theorem sum_semantics (m : Data) (rows : List Data) (hm : Normalized m) (hm0 : m≠[])
    (hrows : ∀ a∈rows,Reduced m a) : semantics (sumRows m rows)=(rows.map semantics).sum := by
  induction rows with
  | nil => rfl
  | cons a rows ih =>
    rw [sumRows,PlayerSpecificAdditiveFieldSemantics.plus m a _ hm hm0 (hrows a List.mem_cons_self) (sum_reduced m rows hm hm0),
      ih (fun a ha => hrows a (List.mem_cons_of_mem _ ha))]
    rfl

theorem sum_height (m : Data) (rows : List Data) (hm : Normalized m) (hm0 : m≠[]) (H : ℕ)
    (hrows : ∀ a∈rows,Reduced m a ∧ HasHeight a H) :
    HasHeight (sumRows m rows) ((H+1)*rows.length+1) := by
  induction rows with
  | nil => exact nil_height _
  | cons a rows ih =>
    have ht:=ih (fun a ha => hrows a (List.mem_cons_of_mem _ ha))
    have hp:=PlayerSpecificShortReduction.plus_height m a (sumRows m rows) hm hm0
      (hrows a List.mem_cons_self).1 (sum_reduced m rows hm hm0) H _ (hrows a List.mem_cons_self).2 ht
    have he : H+((H+1)*rows.length+1)+1=(H+1)*(a::rows).length+1 := by rw [List.length_cons]; ring
    exact he ▸ hp

def Represents {N M : ℕ} (values : Fin N → Data) (endpoints : Fin M → Data)
    (a : Data) (positive : List (Fin N)) (negative : List (Fin M)) : Prop :=
  semantics a=((positive.map values).map semantics).sum-((negative.map endpoints).map semantics).sum

theorem representation_height {N M : ℕ} (m : Data) (values : Fin N → Data) (endpoints : Fin M → Data)
    (a : Data) (positive : List (Fin N)) (negative : List (Fin M))
    (hm : Normalized m) (hm0 : m≠[]) (ha : Reduced m a) (H : ℕ)
    (hv : ∀ j,Reduced m (values j) ∧ HasHeight (values j) H)
    (he : ∀ j,Reduced m (endpoints j) ∧ HasHeight (endpoints j) H)
    (hp : positive.Nodup) (hn : negative.Nodup) (hr : Represents values endpoints a positive negative) :
    HasHeight a ((H+1)*(N+M)+3) := by
  have hpos : ∀ p∈positive.map values,Reduced m p ∧ HasHeight p H := by
    intro p h
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp h
    exact hv j
  have hneg : ∀ p∈negative.map endpoints,Reduced m p ∧ HasHeight p H := by
    intro p h
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp h
    exact he j
  let p:=sumRows m (positive.map values)
  let q:=sumRows m (negative.map endpoints)
  have hpRed : Reduced m p := sum_reduced _ _ hm hm0
  have hqRed : Reduced m q := sum_reduced _ _ hm hm0
  have heq : a=PlayerSpecificAlgebraicField.minus m p q := by
    apply PlayerSpecificShortReduction.normalized_injective _ _ ha.1 (PlayerSpecificAlgebraicField.minus_reduced _ _ _ hm hm0).1
    rw [PlayerSpecificAdditiveFieldSemantics.minus m p q hm hm0 hpRed hqRed,
      sum_semantics _ _ hm hm0 (fun p hp => (hpos p hp).1),
      sum_semantics _ _ hm hm0 (fun p hp => (hneg p hp).1)]
    exact hr
  have hpHeight:=sum_height _ _ hm hm0 H hpos
  have hqHeight:=sum_height _ _ hm hm0 H hneg
  have hheight:=PlayerSpecificShortReduction.minus_height m p q hm hm0 hpRed hqRed _ _ hpHeight hqHeight
  have hpLen : positive.length≤N := by simpa only [Fintype.card_fin] using hp.length_le_card
  have hnLen : negative.length≤M := by simpa only [Fintype.card_fin] using hn.length_le_card
  rw [heq]
  apply mono hheight
  simp only [List.length_map]
  have hs:=Nat.mul_le_mul_left (H+1) (Nat.add_le_add hpLen hnLen)
  nlinarith only [hs]

theorem merge {N M : ℕ} (m : Data) (values : Fin N → Data) (endpoints : Fin M → Data)
    (a b : Data) (pa pb : List (Fin N)) (na nb : List (Fin M)) (j : Fin M)
    (hm : Normalized m) (hm0 : m≠[]) (ha : Reduced m a) (hb : Reduced m b) (he : Reduced m (endpoints j))
    (hra : Represents values endpoints a pa na) (hrb : Represents values endpoints b pb nb) :
    Represents values endpoints (PlayerSpecificAlgebraicField.minus m (PlayerSpecificAlgebraicField.plus m a b) (endpoints j))
      (pa++pb) (na++nb++[j]) := by
  unfold Represents at *
  rw [PlayerSpecificAdditiveFieldSemantics.minus m _ _ hm hm0 (PlayerSpecificAlgebraicField.plus_reduced _ _ _ hm hm0) he,
    PlayerSpecificAdditiveFieldSemantics.plus m a b hm hm0 ha hb,hra,hrb]
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

end Blotto.PlayerSpecificSignedLineage
