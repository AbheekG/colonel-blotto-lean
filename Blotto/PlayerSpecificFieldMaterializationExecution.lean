import Blotto.PlayerSpecificInputArrayExecution

/-! Actual indexed reads materialize the sorted field references as the
rational pair row consumed by sweep preparation. All coordinate copies,
returned rows, index/control words and enclosing reads are priced. -/
namespace Blotto.PlayerSpecificFieldMaterializationExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

def frame {N : ℕ} (j : Fin N) (ids : List (Fin N)) (fields : List (ℚ×ℚ)) : Trace :=
  PlayerSpecificSweepExecution.copyFields fields++[.control j.val,.control ids.length]
def run {N : ℕ} (model : RationalCostModel) (A : ℕ) (v w : FixedArrayTable N ℚ) : List (Fin N) → List (ℚ×ℚ)×ℕ
  | [] => ([],price model [.control 0])
  | j::js =>
    let tail:=run model A v w js
    let field:=(v.read j,w.read j)
    let result:=field::tail.1
    (result,tail.2+price model (copyRow [field.1,field.2])+12*A+price model (frame j (j::js) result))

theorem value {N : ℕ} (model : RationalCostModel) (A : ℕ) (v w : FixedArrayTable N ℚ) (ids : List (Fin N)) :
    (run model A v w ids).1=ids.map (fun j => (v.read j,w.read j)) := by
  induction ids with
  | nil => rfl
  | cons j js ih => simp only [run,ih,List.map_cons]

theorem length {N : ℕ} (model : RationalCostModel) (A : ℕ) (v w : FixedArrayTable N ℚ) (ids : List (Fin N)) :
    (run model A v w ids).1.length=ids.length := by rw [value,List.length_map]

theorem heights {N : ℕ} (model : RationalCostModel) (A H : ℕ) (v w : FixedArrayTable N ℚ)
    (hv : ∀ j,RationalHeight (v.read j) H) (hw : ∀ j,RationalHeight (w.read j) H) (ids : List (Fin N)) :
    PlayerSpecificRationalSweepHeights.FieldsHeight (run model A v w ids).1 H := by
  rw [value]
  intro x hx
  obtain ⟨j,_,rfl⟩:=List.mem_map.mp hx
  exact ⟨hv j,hw j⟩

end Blotto.PlayerSpecificFieldMaterializationExecution
