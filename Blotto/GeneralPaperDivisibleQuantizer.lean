import Blotto.GeneralPaperQuantizerCDF

/-! The paper supplies positive T and K with K dividing T. This entry point
uses B = T/K and changes only the size proofs on the same source array.
The deterministic quantizer retains the original T row identities.
-/
namespace Blotto.GeneralPaperRowQuantizer
open GeneralPaperDictionary
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1500000

def castRows {T U m : ℕ} (h : T=U) (rows : FixedArrayTable T (FixedArrayTable m ℚ)) :
    FixedArrayTable U (FixedArrayTable m ℚ) := h ▸ rows

def castDictionary {T U m K : ℕ} (h : T=U) (d : Dictionary U m K) : Dictionary T m K :=
  h.symm ▸ d

theorem castRows_data {T U m : ℕ} (h : T=U) (rows : FixedArrayTable T (FixedArrayTable m ℚ)) :
    (castRows h rows).data=rows.data := by subst U; rfl

theorem castRows_read {T U m : ℕ} (h : T=U) (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (i : Fin T) :
    (castRows h rows).read (Fin.cast h i)=rows.read i := by subst U; rfl

structure Correct {T m K : ℕ} (rows : FixedArrayTable T (FixedArrayTable m ℚ))
    (d : Dictionary T m K) (hT : 0<T) (hK : 0<K) (budget : ℝ) : Prop where
  balanced : Balanced d
  zero : ∀ j,d.anchor j ⟨0,hK⟩=0
  ordered : ∀ j,Monotone (d.anchor j)
  nonnegative : ∀ j l,0≤d.anchor j l
  row_down : ∀ i j,d.anchor j (d.label i j)≤(rows.read i).read j
  feasible : ∀ i,Feasible budget ((law d hT).realRow i)
  supported : Supported budget (law d hT).law
  closed : ∀ j t,
    closedCDF (law (original rows) hT).law j t ≤ closedCDF (law d hT).law j t ∧
    closedCDF (law d hT).law j t ≤ closedCDF (law (original rows) hT).law j t+1/(K:ℝ)
  strict : ∀ j t,
    strictCDF (law (original rows) hT).law j t ≤ strictCDF (law d hT).law j t ∧
    strictCDF (law d hT).law j t ≤ strictCDF (law (original rows) hT).law j t+1/(K:ℝ)
  security : ∀ (v : Values m) (opposingBudget : ℝ),0≤opposingBudget →
    security v opposingBudget (law d hT).law ≤
      security v opposingBudget (law (original rows) hT).law+1/(K:ℝ)

theorem correct_product {K B m : ℕ} (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (budget : ℝ)
    (hRows : ∀ i,Feasible budget (fun j => ((rows.read i).read j:ℝ))) :
    Correct rows (build hK hB rows) (Nat.mul_pos hK hB) hK budget := by
  have hn (i : Fin (K*B)) (j : Fin m) : 0≤(rows.read i).read j := by
    have h := (hRows i).1 j
    change (0:ℝ)≤((rows.read i).read j:ℝ) at h
    exact_mod_cast h
  exact {
    balanced := balanced hK hB rows
    zero := anchor_zero hK hB rows
    ordered := anchors_ordered hK hB rows hn
    nonnegative := anchors_nonnegative hK hB rows hn
    row_down := row_coordinate_le hK hB rows hn
    feasible := every_row_feasible hK hB rows budget hRows
    supported := law_supported hK hB rows budget hRows
    closed := closed_bounds hK hB rows hn
    strict := strict_bounds hK hB rows hn
    security := security_bound hK hB rows hn }

theorem correct_cast {T K B m : ℕ} (hT : 0<T) (hK : 0<K) (hB : 0<B) (h : T=K*B)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (budget : ℝ)
    (hRows : ∀ i,Feasible budget (fun j => ((rows.read i).read j:ℝ))) :
    Correct rows (castDictionary h (build hK hB (castRows h rows))) hT hK budget := by
  subst T
  exact correct_product hK hB rows budget hRows

theorem divisor_block_pos {T K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T) : 0<T/K :=
  Nat.div_pos (Nat.le_of_dvd hT hDiv) hK

theorem divisor_size {T K : ℕ} (hDiv : K∣T) : T=K*(T/K) :=
  (Nat.mul_div_cancel' hDiv).symm

def buildDivisible {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) : Dictionary T m K :=
  castDictionary (divisor_size hDiv)
    (build hK (divisor_block_pos hT hK hDiv) (castRows (divisor_size hDiv) rows))

theorem divisible_correct {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (budget : ℝ)
    (hRows : ∀ i,Feasible budget (fun j => ((rows.read i).read j:ℝ))) :
    Correct rows (buildDivisible hT hK hDiv rows) hT hK budget :=
  correct_cast hT hK (divisor_block_pos hT hK hDiv) (divisor_size hDiv) rows budget hRows

theorem paired_security_bound {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rowsA rowsB : FixedArrayTable T (FixedArrayTable m ℚ)) (budgetA budgetB : ℝ)
    (hA : ∀ i,Feasible budgetA (fun j => ((rowsA.read i).read j:ℝ)))
    (hB : ∀ i,Feasible budgetB (fun j => ((rowsB.read i).read j:ℝ)))
    (v : Values m) (hBudgetA : 0≤budgetA) (hBudgetB : 0≤budgetB) (delta : ℝ)
    (hSource : security v budgetB (law (original rowsA) hT).law+
      security v budgetA (law (original rowsB) hT).law≤1+delta) :
    security v budgetB (law (buildDivisible hT hK hDiv rowsA) hT).law+
      security v budgetA (law (buildDivisible hT hK hDiv rowsB) hT).law≤1+delta+2/(K:ℝ) := by
  have ha := (divisible_correct hT hK hDiv rowsA budgetA hA).security v budgetB hBudgetB
  have hb := (divisible_correct hT hK hDiv rowsB budgetB hB).security v budgetA hBudgetA
  rw [show 2/(K:ℝ)=1/(K:ℝ)+1/(K:ℝ) by ring]
  linarith only [ha,hb,hSource]

end Blotto.GeneralPaperRowQuantizer
