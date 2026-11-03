import Blotto.GeneralPaperCellPlanPrice

/-! A complete native field preparation constructs each of its eight plans
once and retains the four summaries and both option arrays by reference.
Specification proofs and operand/profile calibration are erased.
-/
namespace Blotto.GeneralPaperFieldPlanPreparation
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {mx my : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ) (p q lambda mu : Summary k)
    (candidateOptions : FixedArrayTable mx ℕ) (responseOptions : FixedArrayTable my ℕ) : GeneralPaperEpochFieldPlan.Plan k × ℕ :=
  let pCells := GeneralPaperCellPlanExecution.unsigned bits index price W k U q lambda candidateOptions
  let qCells := GeneralPaperCellPlanExecution.unsigned bits index price W k U p mu responseOptions
  let lambdaCells := GeneralPaperCellPlanExecution.signed bits index price W k U p candidateOptions
  let muCells := GeneralPaperCellPlanExecution.signed bits index price W k U q responseOptions
  let pOccurrences := GeneralPaperQueryLossExecution.run bits index price W k U q lambda p
  let qOccurrences := GeneralPaperQueryLossExecution.run bits index price W k U p mu q
  let lambdaOccurrences := GeneralPaperSignedUpdateExecution.run bits index price W k U p lambda
  let muOccurrences := GeneralPaperSignedUpdateExecution.run bits index price W k U q mu
  (⟨U,mx,my,p,q,lambda,mu,candidateOptions,responseOptions,
    pCells.1,qCells.1,lambdaCells.1,muCells.1,pOccurrences.1,qOccurrences.1,lambdaOccurrences.1,muOccurrences.1,
    GeneralPaperCellPlanExecution.unsigned_data bits index price W k U q lambda candidateOptions,
    GeneralPaperCellPlanExecution.unsigned_data bits index price W k U p mu responseOptions,
    GeneralPaperCellPlanExecution.signed_data bits index price W k U p candidateOptions,
    GeneralPaperCellPlanExecution.signed_data bits index price W k U q responseOptions,
    GeneralPaperQueryLossExecution.data bits index price W k U q lambda p,
    GeneralPaperQueryLossExecution.data bits index price W k U p mu q,
    GeneralPaperSignedUpdateExecution.data bits index price W k U p lambda,
    GeneralPaperSignedUpdateExecution.data bits index price W k U q mu⟩,
    pCells.2+qCells.2+lambdaCells.2+muCells.2+pOccurrences.2+qOccurrences.2+lambdaOccurrences.2+muOccurrences.2+256*W)

theorem data {mx my : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ) (p q lambda mu : Summary k)
    (candidateOptions : FixedArrayTable mx ℕ) (responseOptions : FixedArrayTable my ℕ) :
    (run bits index price W k U p q lambda mu candidateOptions responseOptions).1=
      GeneralPaperEpochFieldPlan.prepare k U p q lambda mu candidateOptions responseOptions := by
  unfold run GeneralPaperEpochFieldPlan.prepare
  dsimp only
  simp only [GeneralPaperCellPlanExecution.unsigned_data,GeneralPaperCellPlanExecution.signed_data,
    GeneralPaperQueryLossExecution.data,GeneralPaperSignedUpdateExecution.data]

def profile (price : ℕ → ℕ) (W mx my k U : ℕ) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  GeneralPaperCellPlanPrice.unsignedProfile price W mx k U+GeneralPaperCellPlanPrice.unsignedProfile price W my k U+
    GeneralPaperCellPlanPrice.signedProfile price W mx k U+GeneralPaperCellPlanPrice.signedProfile price W my k U+
    GeneralPaperQueryLossPrice.profile price W s k U+GeneralPaperQueryLossPrice.profile price W s k U+
    GeneralPaperSignedUpdatePrice.profile price W s k U+GeneralPaperSignedUpdatePrice.profile price W s k U+256*W

def arithmeticProfile (mx my k : ℕ) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  GeneralPaperCellPlanPrice.unsignedArithmeticProfile mx k+GeneralPaperCellPlanPrice.unsignedArithmeticProfile my k+
    GeneralPaperCellPlanPrice.signedArithmeticProfile mx k+GeneralPaperCellPlanPrice.signedArithmeticProfile my k+
    GeneralPaperQueryLossPrice.arithmeticProfile s k+GeneralPaperQueryLossPrice.arithmeticProfile s k+
    GeneralPaperSignedUpdatePrice.arithmeticProfile s k+GeneralPaperSignedUpdatePrice.arithmeticProfile s k+256

theorem bit_work {mx my : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W k U : ℕ) (p q lambda mu : Summary k) (candidateOptions : FixedArrayTable mx ℕ) (responseOptions : FixedArrayTable my ℕ)
    (hp : ∀ r,p.read r<U) (hq : ∀ r,q.read r<U) (hl : ∀ r,lambda.read r<2*U) (hm : ∀ r,mu.read r<2*U)
    (hx : ∀ r,candidateOptions.read r<U) (hy : ∀ r,responseOptions.read r<U) :
    (run true (fun w => w) price W k U p q lambda mu candidateOptions responseOptions).2≤profile price W mx my k U := by
  have h1 := GeneralPaperCellPlanPrice.unsigned_bit_work price hMono W k U q lambda candidateOptions hq hl hx
  have h2 := GeneralPaperCellPlanPrice.unsigned_bit_work price hMono W k U p mu responseOptions hp hm hy
  have h3 := GeneralPaperCellPlanPrice.signed_bit_work price hMono W k U p candidateOptions hp hx
  have h4 := GeneralPaperCellPlanPrice.signed_bit_work price hMono W k U q responseOptions hq hy
  have h5 := GeneralPaperQueryLossPrice.bit_work price hMono W k U q lambda p hp (fun r => (hq r).le) (fun r => (hl r).le)
  have h6 := GeneralPaperQueryLossPrice.bit_work price hMono W k U p mu q hq (fun r => (hp r).le) (fun r => (hm r).le)
  have h7 := GeneralPaperSignedUpdatePrice.bit_work price hMono W k U p lambda hl (fun r => (hp r).le)
  have h8 := GeneralPaperSignedUpdatePrice.bit_work price hMono W k U q mu hm (fun r => (hq r).le)
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1 h2) h3) h4) h5) h6) h7) h8) _

theorem arithmetic_work {mx my : ℕ} (k U : ℕ) (p q lambda mu : Summary k) (candidateOptions : FixedArrayTable mx ℕ) (responseOptions : FixedArrayTable my ℕ)
    (hp : ∀ r,p.read r<U) (hq : ∀ r,q.read r<U) (hl : ∀ r,lambda.read r<2*U) (hm : ∀ r,mu.read r<2*U)
    (hx : ∀ r,candidateOptions.read r<U) (hy : ∀ r,responseOptions.read r<U) :
    (run false (fun _ => 1) (fun _ => 1) 1 k U p q lambda mu candidateOptions responseOptions).2≤arithmeticProfile mx my k := by
  have h1 := GeneralPaperCellPlanPrice.unsigned_arithmetic_work k U q lambda candidateOptions hq hl hx
  have h2 := GeneralPaperCellPlanPrice.unsigned_arithmetic_work k U p mu responseOptions hp hm hy
  have h3 := GeneralPaperCellPlanPrice.signed_arithmetic_work k U p candidateOptions hp hx
  have h4 := GeneralPaperCellPlanPrice.signed_arithmetic_work k U q responseOptions hq hy
  have h5 := GeneralPaperQueryLossPrice.arithmetic_work k U q lambda p
  have h6 := GeneralPaperQueryLossPrice.arithmetic_work k U p mu q
  have h7 := GeneralPaperSignedUpdatePrice.arithmetic_work k U p lambda
  have h8 := GeneralPaperSignedUpdatePrice.arithmetic_work k U q mu
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1 h2) h3) h4) h5) h6) h7) h8) _

theorem same_data {mx my : ℕ} (price : ℕ → ℕ) (W k U : ℕ) (p q lambda mu : Summary k)
    (candidateOptions : FixedArrayTable mx ℕ) (responseOptions : FixedArrayTable my ℕ) :
    (run true (fun w => w) price W k U p q lambda mu candidateOptions responseOptions).1=
      (run false (fun _ => 1) (fun _ => 1) 1 k U p q lambda mu candidateOptions responseOptions).1 := by
  rw [data,data]

theorem constructed {mx my : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ) (p q lambda mu : Summary k)
    (candidateOptions : FixedArrayTable mx ℕ) (responseOptions : FixedArrayTable my ℕ) :
    GeneralPaperEpochFieldPlan.Constructed (run bits index price W k U p q lambda mu candidateOptions responseOptions).1 := by
  rw [data]
  exact GeneralPaperEpochFieldPlan.prepare_constructed _ _ _ _ _ _ _ _

end Blotto.GeneralPaperFieldPlanPreparation
