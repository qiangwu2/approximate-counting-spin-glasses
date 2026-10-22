import Manuscript.RestrictedHigherRuntime

noncomputable section
namespace Manuscript.SKRuntimeNumeric

theorem truncated (N W R A D count : ℕ) (hA : A≤W) (hRA : R*A≤W) (hD : D≤N)
    (hc : count≤63*(2*N+1)*A+(R*(7000*(N+W+1)^5+29)+35)*A+66*(D+1)+12) :
    count≤10000*(N+W+1)^6 := by
  let Q:=N+W+1
  have hQ : 1≤Q := by dsimp [Q];omega
  have hN : N≤Q := by dsimp [Q];omega
  have hW : W≤Q := by dsimp [Q];omega
  have hD' : D+1≤Q := by dsimp [Q];omega
  have hA' : A≤Q := hA.trans hW
  have hprod : (2*N+1)*A≤3*Q^2 := by
    have hh:=Nat.mul_le_mul (show 2*N+1≤3*Q by omega) hA'
    nlinarith
  have hreps : (R*(7000*Q^5+29)+35)*A≤(7000*Q^5+29)*Q+35*Q := by
    have hh:=Nat.mul_le_mul_left (7000*Q^5+29) (hRA.trans hW)
    nlinarith
  have h2 : Q^2≤Q^6 := Nat.pow_le_pow_right hQ (by omega)
  have h1 : Q≤Q^6 := by simpa using Nat.pow_le_pow_right hQ (show 1≤6 by omega)
  have h16 : 1≤Q^6 := hQ.trans h1
  have hp : Q^5*Q=Q^6 := by ring
  change count≤10000*Q^6
  change count≤63*(2*N+1)*A+(R*(7000*Q^5+29)+35)*A+66*(D+1)+12 at hc
  nlinarith

theorem final_truncated (N M old ctl W graph total : ℕ)
    (hM : M≤old) (hctl : ctl≤old) (hW : W≤old)
    (hgraph : graph≤10000*(N+W+1)^6)
    (htotal : total≤141*M+78*N+9*ctl+graph+400) :
    total≤20000*(N+old+1)^6 := by
  let Q:=N+old+1
  have hQ : 1≤Q := by dsimp [Q];omega
  have hN : N≤Q := by dsimp [Q];omega
  have hM' : M≤Q := by dsimp [Q];omega
  have hctl' : ctl≤Q := by dsimp [Q];omega
  have h1 : Q≤Q^6 := by simpa using Nat.pow_le_pow_right hQ (show 1≤6 by omega)
  have hg : graph≤10000*Q^6 := hgraph.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (show N+W+1≤Q by dsimp [Q];omega) 6))
  change total≤20000*Q^6
  omega

theorem final_exact (N M old ctl weighted total : ℕ)
    (hM : M≤old) (hctl : ctl≤old) (hweighted : weighted≤(old+1)^2)
    (htotal : total≤141*M+78*N+9*ctl+450+
      (59*N+26+(66*N+56)*M+300*(N+1)+400)*weighted) :
    total≤20000*(N+old+1)^6 := by
  let Q:=N+old+1
  have hQ : 1≤Q := by dsimp [Q];omega
  have hbase : 141*M+78*N+461+
      (59*N+26+(66*N+56)*M+300*(N+1)+400)*weighted≤3000*Q^4 :=
    RestrictedHigherRuntime.numeric_overhead N M old weighted _ hM hweighted le_rfl
  have hc : ctl≤Q := by dsimp [Q];omega
  have h1 : Q≤Q^6 := by simpa using Nat.pow_le_pow_right hQ (show 1≤6 by omega)
  have h4 : Q^4≤Q^6 := Nat.pow_le_pow_right hQ (by omega)
  change total≤20000*Q^6
  omega

end Manuscript.SKRuntimeNumeric
