import Blotto.GeneralPaperComparatorParameterPrice

/-! Retain and reuse the actually constructed score, proxy and alphabet
controls. The alphabet view reads three stored fields; its invariant proofs
are erased. Building the view executes no arithmetic parameter constructor.
The data and prices apply to both unit arithmetic and monotone bit models.
-/
namespace Blotto.GeneralPaperPrecallCachePrice
set_option autoImplicit false

structure Cache where
  score : GeneralPaperScoreScaleParameters.Parameters
  proxy : GeneralPaperProxyParameters.Parameters
  comparator : GeneralPaperComparatorParameters.Parameters

def specification (m k : ℕ) : Cache :=
  ⟨GeneralPaperScoreScaleParameters.prepare m k,GeneralPaperProxyParameters.prepare m k,
    GeneralPaperComparatorParameters.prepare m k (GeneralPaperProxyParameters.prepare m k).qbar⟩

def run (primitive : ℕ → ℕ) (W m k : ℕ) : Cache × ℕ :=
  let roots := GeneralPaperProxyParameterPrice.run primitive W m k
  let comparator := GeneralPaperComparatorParameterPrice.run primitive W m k roots.1.2.qbar
  (⟨roots.1.1,roots.1.2,comparator.1⟩,roots.2+comparator.2+48*W)

theorem data (primitive : ℕ → ℕ) (W m k : ℕ) :
    (run primitive W m k).1=specification m k := by
  simp only [run,GeneralPaperProxyParameterPrice.data,GeneralPaperComparatorParameterPrice.data,specification]

def profile (primitive : ℕ → ℕ) (W m k : ℕ) : ℕ :=
  GeneralPaperProxyParameterPrice.profile primitive W m k+
  GeneralPaperComparatorParameterPrice.profile primitive W m k (GeneralPaperProxyParameters.prepare m k).qbar+48*W

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m k : ℕ) :
    (run primitive W m k).2≤profile primitive W m k := by
  have hr := GeneralPaperProxyParameterPrice.work primitive hMono W m k
  have hc := GeneralPaperComparatorParameterPrice.work primitive hMono W m k (GeneralPaperProxyParameters.prepare m k).qbar
  unfold run
  dsimp only
  rw [GeneralPaperProxyParameterPrice.data]
  exact Nat.add_le_add_right (Nat.add_le_add hr hc) (48*W)

def alphabet (m k : ℕ) (c : Cache) (hc : c=specification m k) : GeneralPaperCodeAlphabet.Alphabet where
  D := c.comparator.D
  C := c.comparator.C
  lambda := c.comparator.lambda
  orderPositive := by rw [hc]; exact (GeneralPaperProxyParameters.alphabet m k).orderPositive
  scalePositive := by rw [hc]; exact (GeneralPaperProxyParameters.alphabet m k).scalePositive
  separated := by rw [hc]; exact (GeneralPaperProxyParameters.alphabet m k).separated
  dyadic := by rw [hc]; exact (GeneralPaperProxyParameters.alphabet m k).dyadic

theorem alphabet_data (m k : ℕ) (c : Cache) (hc : c=specification m k) :
    alphabet m k c hc=GeneralPaperProxyParameters.alphabet m k := by
  subst c
  rfl

def prepare (primitive : ℕ → ℕ) (W m k : ℕ) : (Cache × GeneralPaperCodeAlphabet.Alphabet) × ℕ :=
  let controls := run primitive W m k
  ((controls.1,alphabet m k controls.1 (data primitive W m k)),controls.2+24*W)

theorem prepare_data (primitive : ℕ → ℕ) (W m k : ℕ) :
    (prepare primitive W m k).1=(specification m k,GeneralPaperProxyParameters.alphabet m k) := by
  simp only [prepare,data,alphabet_data]

theorem prepare_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m k : ℕ) :
    (prepare primitive W m k).2≤profile primitive W m k+24*W :=
  Nat.add_le_add_right (work primitive hMono W m k) (24*W)

theorem both_data (primitive : ℕ → ℕ) (W m k : ℕ) :
    (prepare primitive W m k).1=(prepare (fun _ => 1) 1 m k).1 := by
  rw [prepare_data,prepare_data]

theorem retained_projections (primitive : ℕ → ℕ) (W m k : ℕ) :
    let c := (prepare primitive W m k).1
    c.1.score.depth=(GeneralPaperScoreScaleParameters.prepare m k).depth ∧
    c.1.proxy.H=(GeneralPaperProxyParameters.prepare m k).H ∧
    c.1.proxy.Qg=(GeneralPaperProxyParameters.prepare m k).Qg ∧
    c.1.proxy.qbar=(GeneralPaperProxyParameters.prepare m k).qbar ∧
    c.2.D=c.1.comparator.D ∧ c.2.C=c.1.comparator.C ∧ c.2.lambda=c.1.comparator.lambda := by
  rw [prepare_data]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end Blotto.GeneralPaperPrecallCachePrice
