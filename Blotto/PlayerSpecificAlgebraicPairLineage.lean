import Blotto.PlayerSpecificAlgebraicPairHeights

/-! Exact lineage continuation for a reached fractional pair. Each
returned resource is zero, a frozen original endpoint, a sum of the old
lineages or that sum minus one selected original endpoint. -/
namespace Blotto.PlayerSpecificAlgebraicPairLineage
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicPairStep PlayerSpecificSignedLineage
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem sum_representation {N M : ℕ} (m : Data) (values : Fin N → Data) (endpoints : Fin M → Data)
    (a b : Data) (pa pb : List (Fin N)) (na nb : List (Fin M))
    (hm : Normalized m) (hm0 : m≠[]) (ha : Reduced m a) (hb : Reduced m b)
    (hra : Represents values endpoints a pa na) (hrb : Represents values endpoints b pb nb) :
    Represents values endpoints (PlayerSpecificAlgebraicField.plus m a b) (pa++pb) (na++nb) := by
  unfold Represents at *
  rw [PlayerSpecificAdditiveFieldSemantics.plus m a b hm hm0 ha hb,hra,hrb]
  simp only [List.map_append,List.sum_append]
  ring

theorem resource_cases (model : RationalCostModel) (root : Candidate) (lengthA lengthB a b c : Data)
    (hc : c∈[(run model root lengthA lengthB a b).upperA,(run model root lengthA lengthB a b).upperB,
      (run model root lengthA lengthB a b).lowerA,(run model root lengthA lengthB a b).lowerB]) :
    c=[] ∨ c=lengthA ∨ c=lengthB ∨ c=PlayerSpecificAlgebraicField.plus root.polynomial a b ∨
      c=PlayerSpecificAlgebraicField.minus root.polynomial (PlayerSpecificAlgebraicField.plus root.polynomial a b) lengthA ∨
      c=PlayerSpecificAlgebraicField.minus root.polynomial (PlayerSpecificAlgebraicField.plus root.polynomial a b) lengthB := by
  dsimp only [PlayerSpecificAlgebraicPairStep.run] at hc
  split at hc <;> split at hc <;>
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc <;>
    rcases hc with rfl|rfl|rfl|rfl <;> simp

theorem surviving_representation {N M : ℕ} (model : RationalCostModel) (root : Candidate)
    (values : Fin N → Data) (endpoints : Fin M → Data) (i j : Fin M) (a b c : Data)
    (pa pb : List (Fin N)) (na nb : List (Fin M))
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (ha : Reduced root.polynomial a) (hb : Reduced root.polynomial b)
    (hi : Reduced root.polynomial (endpoints i)) (hj : Reduced root.polynomial (endpoints j))
    (hra : Represents values endpoints a pa na) (hrb : Represents values endpoints b pb nb)
    (hc : c∈[(run model root (endpoints i) (endpoints j) a b).upperA,(run model root (endpoints i) (endpoints j) a b).upperB,
      (run model root (endpoints i) (endpoints j) a b).lowerA,(run model root (endpoints i) (endpoints j) a b).lowerB])
    (hc0 : c≠[]) (hci : c≠endpoints i) (hcj : c≠endpoints j) :
    Represents values endpoints c (pa++pb) (na++nb) ∨
      Represents values endpoints c (pa++pb) (na++nb++[i]) ∨
      Represents values endpoints c (pa++pb) (na++nb++[j]) := by
  rcases resource_cases model root (endpoints i) (endpoints j) a b c hc with hz|hei|hej|h|h|h
  · exact False.elim (hc0 hz)
  · exact False.elim (hci hei)
  · exact False.elim (hcj hej)
  · rw [h]; exact Or.inl (sum_representation _ _ _ _ _ _ _ _ _ hm hm0 ha hb hra hrb)
  · rw [h]; exact Or.inr (Or.inl (merge _ _ _ _ _ _ _ _ _ i hm hm0 ha hb hi hra hrb))
  · rw [h]; exact Or.inr (Or.inr (merge _ _ _ _ _ _ _ _ _ j hm hm0 ha hb hj hra hrb))

end Blotto.PlayerSpecificAlgebraicPairLineage
