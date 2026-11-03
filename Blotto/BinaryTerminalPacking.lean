import Blotto.BinaryTerminalGrouping
import Blotto.RationalTerminalPacking

/-! Native terminal packing materializes the computed member/total list once.
Its runtime size is the actual group count; exact member and cached-total
correspondence to the retained partition is proved with erased source indices. -/

namespace Blotto.BinaryTerminalPacking
open BinaryRationalNormalization BinaryRationalEncoding BinaryTerminalGrouping

def prepare {n : ℕ} (input : Input n) : FixedArrayTable (groups input).length (List (Fin n) × SignedWord) :=
  ⟨(packed input).toArray,by simp [groups]⟩

theorem prepare_canonical {n : ℕ} (input : Input n) (hC : input.Canonical) :
    ∀ g, CanonicalWord ((prepare input).read g).2 := by
  intro g
  exact packed_canonical input hC _ (List.getElem_mem (by have h:=g.isLt; simpa [groups] using h))

theorem prepare_members {n : ℕ} (input : Input n) (g : Fin (groups input).length) :
    ((prepare input).read g).1 = (groups input).get g := by
  have hg : g.val < (packed input).length := by have h:=g.isLt; simpa [groups] using h
  change ((packed input)[g.val]'hg).1 = _
  change ((packed input)[g.val]'hg).1 = ((packed input).map Prod.fst)[g.val]'(by simpa [groups] using g.isLt)
  rw [List.getElem_map]

theorem prepare_total {n : ℕ} (input : Input n) (source : RationalTerminalLotto n)
    (hC : input.Canonical) (hr : input.Refines source) (g : Fin (groups input).length) :
    value ((prepare input).read g).2 = source.partition.total
      (g.cast (congrArg List.length (groups_refines input source hC hr))) := by
  have he := packed_totals input source hC hr ((prepare input).read g)
    (List.getElem_mem (by have h:=g.isLt; simpa [groups] using h))
  rw [prepare_members] at he
  have hm : (groups input).get g = source.partition.members (g.cast (congrArg List.length (groups_refines input source hC hr))) := by
    change (groups input).get g = source.groups.get _
    have hGroups := groups_refines input source hC hr
    have hGet := List.getElem_of_eq hGroups (i := g.val) g.isLt
    exact hGet
  rw [hm] at he
  exact he.trans (source.partition.total_eq _).symm

end Blotto.BinaryTerminalPacking
