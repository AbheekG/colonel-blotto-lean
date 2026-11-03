import Blotto.PlayerSpecificSegmentSelectionNodeCost

/-! Complete selected-path segment-choice source work. An additive
remaining-mass potential derives every reached quotient/difference size;
the code never receives a probability, height or branch-cost oracle. -/
namespace Blotto.PlayerSpecificSegmentSelectionSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificSegmentSelectionSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem cost {slots : ℕ} (root : Candidate) (weights : FixedArrayTable slots Data) (fallback : Fin slots) (H T S : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmS : HasHeight root.polynomial S) (he : HasHeight [root.interval.lo,root.interval.hi] S) (hv : root.interval.lo<root.interval.hi)
    (hS : 1≤S) (hTS : T≤S) (hw : ∀ j,Reduced root.polynomial (weights.read j) ∧ HasHeight (weights.read j) T)
    (items : List (Fin slots)) : ∀ (remaining : Data) (C : ℕ) (blocks : List (Fin H → Bool)),
    Reduced root.polynomial remaining → HasHeight remaining C → C+(items.length+1)*(T+1)≤S → items.length≤slots → blocks.length≤slots →
    (PlayerSpecificSegmentSelectionExecution.select RationalCostModel.schoolbook root weights fallback H items remaining blocks).2≤
      (items.length+1)*work S H slots := by
  let model:=RationalCostModel.schoolbook
  let X:=(size S H slots+1)^3
  let R:=PlayerSpecificResourceCostProfile.rationalCoefficient
  let Q:=PlayerSpecificAlgebraicCoinCost.polynomialCoefficient
  have hwS : ∀ j,Reduced root.polynomial (weights.read j) ∧ HasHeight (weights.read j) S :=
    fun j => ⟨(hw j).1,mono (hw j).2 hTS⟩
  intro remaining C blocks hr hrC hpotential hi hb
  induction items generalizing remaining C blocks with
  | nil =>
    have hrS : Reduced root.polynomial remaining ∧ HasHeight remaining S := ⟨hr,mono hrC (by omega)⟩
    have hf:=PlayerSpecificSegmentSelectionFramePolynomial.cost root weights fallback H [] remaining [] [] blocks.length (fallback,0) S hmS hml he
      hwS hrS ⟨nil_reduced _ hm0,nil_height _⟩ ⟨nil_reduced _ hm0,nil_height _⟩ hi hb (by omega)
    rw [List.length_nil,Nat.zero_add,Nat.one_mul]
    exact hf.trans (frame_profile R Q slots X)
  | cons slot rest ih =>
    simp only [List.length_cons] at hpotential hi
    have hCS : C≤S := by omega
    have hrS : Reduced root.polynomial remaining ∧ HasHeight remaining S := ⟨hr,mono hrC hCS⟩
    let p:=PlayerSpecificFieldDivisionExecution.run model root.polynomial (weights.read slot) remaining
    let coin:=PlayerSpecificAlgebraicCoinExecution.run model root p.1 H (blocks.headD (fun _ => false))
    have hp:=PlayerSpecificSegmentSelectionNodeCost.probability root (weights.read slot) remaining S H slots (blocks.headD (fun _ => false))
      hm hm0 hml hmS he hv (hwS slot) hrS hS
    have hprob : p.2≤(8000000000*R)*X := hp.2.2.1
    have hcoin : coin.2≤Q*X := hp.2.2.2
    simp only [PlayerSpecificSegmentSelectionExecution.select]
    split
    · have hf:=PlayerSpecificSegmentSelectionFramePolynomial.cost root weights fallback H (slot::rest) remaining p.1 [] blocks.length (slot,1) S
        hmS hml he hwS hrS ⟨hp.1,hp.2.1⟩ ⟨nil_reduced _ hm0,nil_height _⟩ (by simpa only [List.length_cons] using hi) hb (by omega)
      have hlocal : p.2+coin.2+price model (PlayerSpecificSegmentSelectionExecution.frame root weights fallback H (slot::rest) remaining p.1 [] blocks.length (slot,1))≤
          work S H slots :=
        (Nat.add_le_add (Nat.add_le_add hprob hcoin) hf).trans (accepted_profile R Q slots X)
      have hpad:=Nat.mul_le_mul_right (work S H slots) (show 1≤rest.length+1+1 by omega)
      exact hlocal.trans (by simpa only [Nat.one_mul,List.length_cons] using hpad)
    · let next:=PlayerSpecificFieldCombination.run true root.polynomial remaining (weights.read slot)
      have hn : Reduced root.polynomial next.1 := PlayerSpecificFieldCombination.reduced true _ _ _ hm hm0
      have hnC : HasHeight next.1 (C+T+1) := by
        rw [PlayerSpecificFieldCombination.value]
        change HasHeight (PlayerSpecificAlgebraicField.minus root.polynomial remaining (weights.read slot)) _
        exact PlayerSpecificShortReduction.minus_height _ _ _ hm hm0 hr (hw slot).1 C T hrC (hw slot).2
      have hnextPot : C+T+1+(rest.length+1)*(T+1)≤S := by nlinarith only [hpotential]
      have hnS : HasHeight next.1 S := mono hnC (by nlinarith only [hpotential,Nat.zero_le (rest.length*(T+1))])
      let tail:=PlayerSpecificSegmentSelectionExecution.select model root weights fallback H rest next.1 blocks.tail
      have htail : tail.2≤(rest.length+1)*work S H slots := ih next.1 (C+T+1) blocks.tail hn hnC hnextPot
        (by omega) (by rw [List.length_tail]; omega)
      have htailVisits : tail.1.2≤rest.length := PlayerSpecificSegmentSelectionExecution.visits model root weights fallback H rest next.1 blocks.tail
      have hd:=PlayerSpecificSegmentSelectionNodeCost.difference root remaining (weights.read slot) S H slots hm hm0 hml hmS hrS (hwS slot) hS
      have hf:=PlayerSpecificSegmentSelectionFramePolynomial.cost root weights fallback H (slot::rest) remaining p.1 next.1 blocks.length (tail.1.1,tail.1.2+1) S
        hmS hml he hwS hrS ⟨hp.1,hp.2.1⟩ ⟨hn,hnS⟩ (by simpa only [List.length_cons] using hi) hb (by omega)
      have hlocal : p.2+coin.2+price model next.2+
          price model (PlayerSpecificSegmentSelectionExecution.frame root weights fallback H (slot::rest) remaining p.1 next.1 blocks.length (tail.1.1,tail.1.2+1))≤work S H slots :=
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hprob hcoin) hd) hf).trans (node_profile R Q slots X)
      change p.2+coin.2+price model next.2+tail.2+
        price model (PlayerSpecificSegmentSelectionExecution.frame root weights fallback H (slot::rest) remaining p.1 next.1 blocks.length (tail.1.1,tail.1.2+1))≤_
      have hsum:=Nat.add_le_add hlocal htail
      have hbound : work S H slots+(rest.length+1)*work S H slots=(rest.length+1+1)*work S H slots := by ring
      have hfinal:=hsum.trans_eq hbound
      simp only [List.length_cons]
      omega

end Blotto.PlayerSpecificSegmentSelectionSourceCost
