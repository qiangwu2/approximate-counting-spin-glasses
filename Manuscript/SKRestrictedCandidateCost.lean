import Manuscript.SKRestrictedCandidateExecution

/-! A uniform polynomial envelope for the genuine candidate-machine trace.
The exponential state dimension is explicit; no operation count is assumed. -/
noncomputable section
namespace Manuscript.SKRestrictedCandidateCost
open SKCandidateLayout

def expanded (N B K P M : ℕ) : ℕ :=
  (9*K+36+(B+N)*(30*N+(9*K+30*(P*N)+K*((P*N)*(38*K+27*N+137)+21)+35)+30*(P*N)+100+5)+
    (9*(K+B)+100)+
    (30*M+(B*B)*P*(27*N+58*K+18*B+229)+P*(N*(27*N+18)+58*K+147)+55))+
  (B*B*(30*M+18*B+141)+10+M^2*(52*B+29*K+157)+11+
    (K+B*B)*(56*M^2+90*M+111)+90*M+104+M*(40*B+53*K+110)+8+100)

theorem operationBound_eq (d : Layout) : SKRestrictedCandidateExecution.operationBound d=
    expanded d.root.N d.root.B d.root.K (2^d.root.K) d.M := rfl

theorem expanded_mono {N B K P M X : ℕ} (hN : N≤X) (hB : B≤X) (hK : K≤X)
    (hP : P≤X) (hM : M≤X) : expanded N B K P M≤expanded X X X X X := by
  unfold expanded
  gcongr

theorem diagonal_bound (X : ℕ) (hX : 1≤X) : expanded X X X X X≤10000*X^5 := by
  have h0 : 1≤X^5 := one_le_pow₀ hX
  have h1 : X≤X^5 := by simpa using Nat.pow_le_pow_right hX (show 1≤5 by omega)
  have h2 : X^2≤X^5 := Nat.pow_le_pow_right hX (by omega)
  have h3 : X^3≤X^5 := Nat.pow_le_pow_right hX (by omega)
  have h4 : X^4≤X^5 := Nat.pow_le_pow_right hX (by omega)
  unfold expanded
  nlinarith

theorem operationBound_le (d : Layout) : SKRestrictedCandidateExecution.operationBound d≤
    10000*(d.root.N+d.root.B+d.root.K+d.M+1)^5 := by
  let X := d.root.N+d.root.B+d.root.K+d.M+1
  have hP : 2^d.root.K≤d.M := by
    have hQ : 1≤6^d.root.B := one_le_pow₀ (by omega)
    unfold Layout.M
    calc
      2^d.root.K≤(d.root.K+1)*2^d.root.K := by nlinarith [Nat.zero_le (d.root.K*2^d.root.K)]
      _≤(d.root.K+1)*2^d.root.K*6^d.root.B := Nat.le_mul_of_pos_right _ (by omega)
  rw [operationBound_eq]
  exact (expanded_mono (X:=X) (by dsimp [X]; omega) (by dsimp [X]; omega)
    (by dsimp [X]; omega) (by dsimp [X]; omega) (by dsimp [X]; omega)).trans
    (diagonal_bound X (by dsimp [X]; omega))
end Manuscript.SKRestrictedCandidateCost
