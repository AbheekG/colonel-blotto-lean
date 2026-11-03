import Blotto.GeneralPaperSourceEndpointSize

/-! Literal decoded dictionary size, including its distinguished zero
labels and the immediate all-zero branch. Bounds are on reduced stored
rationals, with a common denominator free of the initialization scale.
-/
namespace Blotto.GeneralPaperEndpointDictionarySize
open GeneralPaperProxyParameters GeneralPaperEndpointDictionary
set_option autoImplicit false
set_option maxHeartbeats 3500000

def width (m k : ℕ) : ℕ := binaryWordWidth (prepare m k).qbar+binaryWordWidth (prepare m k).H

theorem width_positive (m k : ℕ) : 0<width m k := by
  have hh := binaryWordWidth_pos (prepare m k).H
  unfold width
  omega

theorem width_bound (m k : ℕ) : width m k≤6+3*binaryWordWidth (prepare m k).H := by
  have hh := GeneralPaperProxyWidths.cap_width m k
  unfold width
  omega

theorem dimension_bound (m k : ℕ) : width m k≤9+3*((prepare m k).d+2)*binaryWordWidth (m+3) := by
  have hh := GeneralPaperProxyWidths.H_width m k
  have hw := width_bound m k
  nlinarith only [hh,hw]

def Contract {T m : ℕ} (k : ℕ) (result : GeneralPaperSourceEndpointBranch.Result T m (prepare m k).K) : Prop :=
  (∀ j l,RationalHeight ((dictionary result).anchor j l) (width m k)) ∧
    match result.choice with
    | .zero => True
    | .endpoint gamma _ => ∃ D,0<D ∧ D≤(prepare m k).H ∧
        ∀ j l,OnRationalLattice (gamma.den*D) ((dictionary result).anchor j l)

theorem zero {T m : ℕ} (k : ℕ) (labels : Fin T → Fin m → Fin (prepare m k).K) :
    Contract k ⟨labels,.zero⟩ := by
  refine ⟨?_,trivial⟩
  intro j l
  rw [zero_anchors]
  exact GeneralPaperQuantizedHeight.zero_height _ (width_positive m k)

theorem endpoint_entries {T m : ℕ} (k : ℕ) (labels : Fin T → Fin m → Fin (prepare m k).K)
    (gamma : ℚ) (point : GeneralPaperBasisRationalSolve.RatVector (m*((prepare m k).K-1))) (D : ℕ)
    (hc : GeneralPaperSourceEndpointSize.Contract k gamma point D) (j : Fin m) (l : Fin (prepare m k).K) :
    OnRationalLattice (gamma.den*D) ((dictionary ⟨labels,.endpoint gamma point⟩).anchor j l) ∧
      RationalHeight ((dictionary ⟨labels,.endpoint gamma point⟩).anchor j l) (width m k) := by
  let result : GeneralPaperSourceEndpointBranch.Result T m (prepare m k).K := ⟨labels,.endpoint gamma point⟩
  change OnRationalLattice (gamma.den*D) ((dictionary result).anchor j l) ∧ RationalHeight ((dictionary result).anchor j l) _
  by_cases hl : l.val=0
  · have he : (dictionary result).anchor j l=0 := by
      change anchor result j l=0
      simp only [anchor,hl,dite_true]
    rw [he]
    exact ⟨by simp [OnRationalLattice],GeneralPaperQuantizedHeight.zero_height _ (width_positive m k)⟩
  · let a : RationalOrderCell.Variable m (prepare m k).K := (j,⟨l.val-1,by have hh := l.isLt; omega⟩)
    have he : GeneralPaperTransferPolytopePoint.positiveLabel a.2=l := by
      apply Fin.ext
      change l.val-1+1=l.val
      omega
    rw [←he,positive_label]
    exact hc.2.2 a

theorem endpoint {T m : ℕ} (k : ℕ) (labels : Fin T → Fin m → Fin (prepare m k).K)
    (gamma : ℚ) (point : GeneralPaperBasisRationalSolve.RatVector (m*((prepare m k).K-1))) (D : ℕ)
    (hc : GeneralPaperSourceEndpointSize.Contract k gamma point D) :
    Contract k ⟨labels,.endpoint gamma point⟩ := by
  have he := endpoint_entries k labels gamma point D hc
  exact ⟨fun j l => (he j l).2,D,hc.1,hc.2.1,fun j l => (he j l).1⟩

end Blotto.GeneralPaperEndpointDictionarySize
