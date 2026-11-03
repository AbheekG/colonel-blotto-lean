import Blotto.BinaryPRGHeapSeedOutputLifetime
import Blotto.BinaryPRGFrameCostJoin
import Blotto.NaturalPolynomialEnvelope

/-! Uniform polynomial growth for the complete optional PRG continuation,
global fallback and original-budget scaling/framing. These are conservative
retained source-cell/activation bounds, not sharp powers or host-byte bounds.
Raw input production is outside this trace; successful parsing is used only
to derive its original source/dimension/precision/header parameters. -/
namespace Blotto.BinaryPRGFullOutputLifetimePolynomial
open BinaryPRGHeapTraceUsage BinarySeedPreparationSpace RationalLottoResourceSystem
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000

structure Parameters where
  count : ℕ
  height : ℕ
  precision : ℕ
  indexWidth : ℕ
  seedCap : ℕ
  headerLength : ℕ

def inputSize (p : Parameters) : ℕ :=
  p.count+p.height+p.precision+p.indexWidth+p.seedCap+p.headerLength

-- Expand only project formula definitions. Each closure step constructs a
-- proof using NaturalPolynomialEnvelope; no runtime contract is inferred.
open Lean Meta Elab Tactic in
elab "output_lifetime_polynomial" : tactic => do
  for _ in [:100000] do
    if (← getGoals).isEmpty then return
    evalTactic (← `(tactic| try dsimp only))
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    let fn := target.getAppArgs.back!
    let body := match fn with
      | .lam _ _ body _ => body.headBeta
      | _ => fn
    let head := body.getAppFn.constName?
    let rule ← match head with
      | some ``Parameters.count | some ``Parameters.height | some ``Parameters.precision
      | some ``Parameters.indexWidth | some ``Parameters.seedCap | some ``Parameters.headerLength =>
          `(tactic| exact NaturalPolynomialEnvelope.of_le_size _ _ (fun _ => by unfold inputSize; omega))
      | some ``HAdd.hAdd => `(tactic| apply NaturalPolynomialEnvelope.add)
      | some ``HMul.hMul => `(tactic| apply NaturalPolynomialEnvelope.mul)
      | some ``HPow.hPow => `(tactic| apply NaturalPolynomialEnvelope.pow)
      | some ``HSub.hSub => `(tactic| apply NaturalPolynomialEnvelope.sub)
      | some ``Max.max => `(tactic| apply NaturalPolynomialEnvelope.max)
      | some ``expressionHeightBudget => `(tactic| apply NaturalPolynomialEnvelope.height)
      | some ``binaryWordWidth => `(tactic| apply NaturalPolynomialEnvelope.wordWidth)
      | _ =>
          if !body.hasLooseBVars then `(tactic| exact NaturalPolynomialEnvelope.constant _ _)
          else match head with
            | some name =>
                if (`Blotto).isPrefixOf name then `(tactic| unfold $(mkIdent name))
                else throwError "unhandled output lifetime formula head: {repr head}"
            | none => throwError "unhandled output lifetime formula head: {repr head}"
    evalTactic rule
  throwError "output lifetime formula exceeds structural step budget"

def continuationEnvelope (n s K i b header : ℕ) : ℕ :=
  let W := 1+2*expressionHeightBudget (max (3+s) (K+2)) 75
  BinaryWordTerminalLifetime.envelope n (4*(s+2)) K i b b+
    BinaryPRGGlobalFallbackLifetime.envelope n+
    BinaryQuadraticOutputLifetime.bound n W header+
    BinaryQuadraticOutputLifetime.frames n W header+480

theorem continuation_polynomial : NaturalPolynomialEnvelope inputSize (fun p =>
    continuationEnvelope p.count p.height p.precision p.indexWidth p.seedCap p.headerLength) := by
  unfold continuationEnvelope
  output_lifetime_polynomial

theorem framed_envelope_decomposition {n : ℕ} (request : BinaryPRGRequest.Request n) (K i b header : ℕ) :
    BinaryPRGHeapFramedLifetime.envelope request K i b header =
      BinaryPRGHeapCachedPrefixLifetime.envelope request i b+
        continuationEnvelope n request.source.originalInputWordWidth K i b header := by
  unfold BinaryPRGHeapFramedLifetime.envelope BinaryPRGHeapFixedLifetime.envelope
    BinaryPRGHeapTerminalLifetime.envelope BinaryPRGHeapCertifiedPrefixLifetime.envelope
    BinaryCachedGroupInputHeight.inputHeight BinaryPRGHeapFixedProperties.wordWidth
    BinaryPRGOutputPrimitiveWork.normalizedHeight continuationEnvelope
  ring

theorem framed_envelope_polynomial : ∃ C d : ℕ,∀ {n : ℕ} (request : BinaryPRGRequest.Request n) (K i b header : ℕ),
    BinaryPRGHeapFramedLifetime.envelope request K i b header ≤
      C*(n+request.source.originalInputWordWidth+K+i+b+header+2)^d := by
  rcases continuation_polynomial with ⟨C₂,d₂,h₂⟩
  rcases BinaryPRGHeapCallerLifetimePolynomial.uniform_cached_envelope with ⟨C₁,d₁,h₁⟩
  refine ⟨C₁+C₂,d₁+d₂,?_⟩
  intro n request K i b header
  let X := n+request.source.originalInputWordWidth+K+i+b+header+2
  have hX : 0 < X := by dsimp [X]; omega
  have hA := h₁ request i b
  have hB := h₂ ⟨n,request.source.originalInputWordWidth,K,i,b,header⟩
  change continuationEnvelope n request.source.originalInputWordWidth K i b header ≤
    C₂*(n+request.source.originalInputWordWidth+K+i+b+header+1)^d₂ at hB
  have hp₁ : (n+request.source.originalInputWordWidth+i+b+2)^d₁ ≤ X^(d₁+d₂) :=
    (Nat.pow_le_pow_left (by dsimp [X]; omega) d₁).trans (Nat.pow_le_pow_right hX (by omega))
  have hp₂ : (n+request.source.originalInputWordWidth+K+i+b+header+1)^d₂ ≤ X^(d₁+d₂) :=
    (Nat.pow_le_pow_left (by dsimp [X]; omega) d₂).trans (Nat.pow_le_pow_right hX (by omega))
  have h₁' := Nat.mul_le_mul_left C₁ hp₁
  have h₂' := Nat.mul_le_mul_left C₂ hp₂
  rw [framed_envelope_decomposition]
  change _ ≤ (C₁+C₂)*X^(d₁+d₂)
  nlinarith

end Blotto.BinaryPRGFullOutputLifetimePolynomial
