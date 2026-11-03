import Blotto.PlayerSpecificAlgebraicExpressionPrimitiveCost

/-! Analysis of the actual interpreter frames using its already proved
native values. These definitions are proof-side source ledgers; the
executing interpreter retains its cached children and selected return. -/
namespace Blotto.PlayerSpecificAlgebraicExpressionFrames
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def rows {k : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (e : RationalExpression k) : List Data :=
  let value:=PlayerSpecificAlgebraicExpression.run model root env
  match e with
  | .input _ => [value e]
  | .literal q => [[q],value e]
  | .add a b | .sub a b | .mul a b | .div a b | .minimum a b | .maximum a b | .ifLe a b _ _ => [value a,value b,value e]

def words {k : ℕ} : RationalExpression k → List ℕ
  | .input j => [k,j.val,1]
  | .literal _ => [k,2]
  | .add _ _ => [k,3]
  | .sub _ _ => [k,4]
  | .mul _ _ => [k,5]
  | .div _ _ => [k,6]
  | .minimum _ _ => [k,7]
  | .maximum _ _ => [k,8]
  | .ifLe _ _ _ _ => [k,9]

def price {k : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data) (e : RationalExpression k) : ℕ :=
  PlayerSpecificRationalTrace.price model (PlayerSpecificAlgebraicExpressionExecution.frame root (rows model root env e) (words e))

theorem row_bounds {k : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (e : RationalExpression k) (S : ℕ) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j)) (hLit : e.LiteralHeights S)
    (hAll : PlayerSpecificAlgebraicExpressionNodes.All (fun a => HasHeight (PlayerSpecificAlgebraicExpression.run model root env a) S) e) :
    ∀ row∈rows model root env e,HasHeight row S ∧ row.length≤3 := by
  have hlen : ∀ a : RationalExpression k,(PlayerSpecificAlgebraicExpression.run model root env a).length≤3 := by
    intro a
    have h:=(PlayerSpecificAlgebraicExpression.reduced model root env a hm hm0 hEnv).2
    omega
  cases e with
  | input j =>
    intro row hrow
    simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at hrow
    rw [hrow]
    exact ⟨hAll.1,hlen _⟩
  | literal q =>
    intro row hrow
    simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at hrow
    rcases hrow with hrow|hrow
    · rw [hrow]
      exact ⟨cons_height hLit (nil_height _),by simp⟩
    · rw [hrow]
      exact ⟨hAll.1,hlen _⟩
  | add a b | sub a b | mul a b | div a b | minimum a b | maximum a b =>
    intro row hrow
    simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at hrow
    rcases hrow with hrow|hrow|hrow
    · rw [hrow]; exact ⟨PlayerSpecificAlgebraicExpressionNodes.head _ a hAll.2.1,hlen _⟩
    · rw [hrow]; exact ⟨PlayerSpecificAlgebraicExpressionNodes.head _ b hAll.2.2,hlen _⟩
    · rw [hrow]; exact ⟨hAll.1,hlen _⟩
  | ifLe a b yes no =>
    intro row hrow
    simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at hrow
    rcases hrow with hrow|hrow|hrow
    · rw [hrow]; exact ⟨PlayerSpecificAlgebraicExpressionNodes.head _ a hAll.2.1,hlen _⟩
    · rw [hrow]; exact ⟨PlayerSpecificAlgebraicExpressionNodes.head _ b hAll.2.2.1,hlen _⟩
    · rw [hrow]; exact ⟨hAll.1,hlen _⟩

theorem bound {k : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (e : RationalExpression k) (S : ℕ) (hk : k≤S) (hS : 10≤S)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmS : HasHeight root.polynomial S) (he : HasHeight [root.interval.lo,root.interval.hi] S)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j)) (hLit : e.LiteralHeights S)
    (hAll : PlayerSpecificAlgebraicExpressionNodes.All (fun a => HasHeight (PlayerSpecificAlgebraicExpression.run model root env a) S) e) :
    price model root env e≤500*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  have hr:=row_bounds model root env e S hm hm0 hml hEnv hLit hAll
  apply PlayerSpecificAlgebraicExpressionPrimitiveCost.frame_cost model root _ _ S hmS he hml
    (fun row hrow => (hr row hrow).1) (fun row hrow => (hr row hrow).2)
  · intro word hw
    cases e <;> simp only [words,List.mem_cons,List.not_mem_nil,or_false] at hw <;>
      rcases hw with hw|hw|hw <;> omega
  · cases e <;> simp only [rows,List.length_cons,List.length_nil] <;> omega
  · cases e <;> simp only [words,List.length_cons,List.length_nil] <;> omega

end Blotto.PlayerSpecificAlgebraicExpressionFrames
