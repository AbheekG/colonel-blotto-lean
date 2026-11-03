import Blotto.GeneralPaperSourceEndpointBranch

/-! Literal dictionary readers for the selected modified-defender result.
Zero outputs decode to zero; endpoint outputs read the already-stored
packed rational point. Original whole-row labels are retained verbatim.
-/
namespace Blotto.GeneralPaperEndpointDictionary
open RationalOrderCell GeneralPaperSourceEndpointBranch GeneralPaperBasisCoordinates
set_option autoImplicit false
set_option maxHeartbeats 3500000

def coordinates {T m K : ℕ} (result : Result T m K) : Variable m K → ℚ :=
  match result.choice with
  | .zero => fun _ => 0
  | .endpoint _ point => GeneralPaperBasisOriginalDirection.reader point

def anchor {T m K : ℕ} (result : Result T m K) (j : Fin m) (l : Fin K) : ℚ :=
  if h : l.val=0 then 0 else coordinates result (j,⟨l.val-1,by have hl := l.isLt; omega⟩)

def dictionary {T m K : ℕ} (result : Result T m K) : GeneralPaperDictionary.Dictionary T m K :=
  ⟨result.labels,anchor result⟩

theorem labels {T m K : ℕ} (result : Result T m K) : (dictionary result).label=result.labels := rfl

theorem zero_label {T m K : ℕ} (result : Result T m K) (hK : 0<K) (j : Fin m) :
    (dictionary result).anchor j ⟨0,hK⟩=0 := by
  simp only [dictionary,anchor,dite_true]

theorem positive_label {T m K : ℕ} (result : Result T m K) (j : Fin m) (l : Fin (K-1)) :
    (dictionary result).anchor j (GeneralPaperTransferPolytopePoint.positiveLabel l)=coordinates result (j,l) := by
  have hn : (GeneralPaperTransferPolytopePoint.positiveLabel l).val≠0 := by
    change l.val+1≠0
    omega
  change anchor result j (GeneralPaperTransferPolytopePoint.positiveLabel l)=_
  rw [anchor,dite_eq_right hn]
  apply congrArg (coordinates result)
  apply Prod.ext rfl
  apply Fin.ext
  change (l.val+1)-1=l.val
  omega

theorem real_coordinates {T m K : ℕ} (result : Result T m K) :
    GeneralPaperTransferPolytopePoint.coordinates (dictionary result)=fun a => (coordinates result a:ℝ) := by
  funext a
  simp only [GeneralPaperTransferPolytopePoint.coordinates,positive_label]

theorem zero_anchors {T m K : ℕ} (originalLabels : Fin T → Fin m → Fin K) (j : Fin m) (l : Fin K) :
    (dictionary (⟨originalLabels,.zero⟩ : Result T m K)).anchor j l=0 := by
  change anchor (⟨originalLabels,.zero⟩ : Result T m K) j l=0
  unfold anchor
  split <;> rfl

theorem endpoint_coordinates {T m K : ℕ} (originalLabels : Fin T → Fin m → Fin K) (gamma : ℚ)
    (point : GeneralPaperBasisRationalSolve.RatVector (m*(K-1))) (a : Variable m K) :
    coordinates (⟨originalLabels,.endpoint gamma point⟩ : Result T m K) a=point.read (index a) := rfl

end Blotto.GeneralPaperEndpointDictionary
