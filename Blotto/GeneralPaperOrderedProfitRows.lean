import Blotto.GeneralPaperOrderedNativeProfitOptimizer
import Blotto.GeneralPaperResponseTagSums

/-! Backtracked tuples select one actual option per ordered field. Their
resource and input profit are exactly the sums read from those fields. This
links the retained predecessor semantics to ordinary complete row semantics.
-/
namespace Blotto.GeneralPaperOrderedProfitRows
open GeneralPaperOrderedProfitDP GeneralPaperOrderedProfitSound GeneralPaperOrderedProfitTreeBuild
set_option autoImplicit false
variable {R : Type} [LinearOrder R] [AddCommMonoid R] [IsOrderedAddMonoid R]

def resources {K : ℕ} (fs : List (Field R K)) (labels : List (Fin K)) : List R :=
  (fs.zip labels).map (fun p => (p.1.read p.2).2)

def profits {K : ℕ} (fs : List (Field R K)) (labels : List (Fin K)) : List ℕ :=
  (fs.zip labels).map (fun p => (p.1.read p.2).1)

theorem resources_append {K : ℕ} (left right : List (Field R K)) (ll rr : List (Fin K)) (hLen : left.length=ll.length) :
    resources (left++right) (ll++rr)=resources left ll++resources right rr := by
  rw [resources,List.zip_append hLen,List.map_append]
  rfl

theorem profits_append {K : ℕ} (left right : List (Field R K)) (ll rr : List (Fin K)) (hLen : left.length=ll.length) :
    profits (left++right) (ll++rr)=profits left ll++profits right rr := by
  rw [profits,List.zip_append hLen,List.map_append]
  rfl

theorem fields_length {K h : ℕ} (tree : Tree R K h) : (fields tree).length=2^h := by
  induction tree with
  | leaf field => rfl
  | @node h left right ihl ihr =>
    simp only [fields,List.length_append,ihl,ihr,pow_succ]
    omega

theorem realizes_sums {K h : ℕ} (tree : Tree R K h) (labels : List (Fin K)) (cost : R) (P : ℕ)
    (hRealizes : Realizes tree labels cost P) :
    (resources (fields tree) labels).sum=cost ∧ (profits (fields tree) labels).sum=P := by
  induction tree generalizing labels cost P with
  | leaf field =>
    obtain ⟨a,rfl,rfl,rfl⟩ := hRealizes
    simp [fields,resources,profits]
  | node left right ihl ihr =>
    obtain ⟨ll,lc,lp,rr,rc,rp,hl,hr,rfl,rfl,rfl⟩ := hRealizes
    have hLen := (fields_length left).trans (realizes_length left ll lc lp hl).symm
    obtain ⟨hcl,hpl⟩ := ihl ll lc lp hl
    obtain ⟨hcr,hpr⟩ := ihr rr rc rp hr
    simp only [fields,resources_append _ _ _ _ hLen,profits_append _ _ _ _ hLen,List.sum_append,hcl,hcr,hpl,hpr,and_self]

end Blotto.GeneralPaperOrderedProfitRows
