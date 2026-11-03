import Blotto.GeneralPaperRayOriginalResidual

/-! Native original-row blocker descriptors. Static blockers retain their
original index; high blockers retain the recovered indexed whole tuple.
The score proof places the latter in the original high-row family.
-/
namespace Blotto.GeneralPaperRayBlockerRows
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperStaticRayRows
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000

abbrev Descriptor (T m K : ℕ) := StaticIndex T m K ⊕ FixedArrayTable m (Fin K)

def row {T m K : ℕ} (labels : Fin T → Fin m → Fin K) : Descriptor T m K → Row (Variable m K)
  | .inl i => GeneralPaperStaticRayRows.row labels i
  | .inr tuple => ⟨(rawRow (fun _ => 0) (.inr (tuple.read,0))).neg.terms,0,-1⟩

theorem static_original {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (h : ℕ)
    (i : StaticIndex T m K) : ∃ index,row labels (.inl i)=constraints labels scores h index :=
  ⟨embed i,GeneralPaperStaticRayRows.row_eq labels scores h i⟩

theorem high_original {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (h : ℕ)
    (tuple : FixedArrayTable m (Fin K)) (hHigh : h<∑ j,scores j (tuple.read j)) :
    ∃ index,row labels (.inr tuple)=constraints labels scores h index := ⟨.inr (.inr (.inr ⟨tuple.read,hHigh⟩)),rfl⟩

theorem high_value {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (scores : Fin m → Fin K → ℕ) (h : ℕ)
    (tuple : FixedArrayTable m (Fin K)) (hHigh : h<∑ j,scores j (tuple.read j))
    (beta : ℚ) (x w : Variable m K → ℚ) (t : ℚ) :
    (GeneralPaperRayOriginalResidual.evaluate (row labels (.inr tuple)) beta x w).value t=
      (GeneralPaperRayTupleResidual.residual x w beta tuple.read).value t :=
  GeneralPaperRayOriginalResidual.high_value labels scores h ⟨tuple.read,hHigh⟩ beta x w t

end Blotto.GeneralPaperRayBlockerRows
