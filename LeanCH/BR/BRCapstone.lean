import LeanCH.BR.Compose.Boundary

/-! The all-parameter boundary-regularity hypothesis implies the literal CH proposition. -/

namespace Compose.Boundary

/-- It suffices to prove boundary regularity at every positive pair of parameters. -/
theorem caccettaHaggkvist_of_boundaryRegular
    (hBR : ∀ q s, 0 < q → 0 < s → BoundaryRegular q s) :
    CH.CaccettaHaggkvistConjecture := by
  intro n s G hn hs hloop hdeg
  have hnq : n ≤ CH.ceilDiv n s * s := by
    have hmod := Nat.mod_lt (n + s - 1) hs
    have hdiv := Nat.mod_add_div (n + s - 1) s
    rw [Nat.mul_comm s] at hdiv
    unfold CH.ceilDiv
    omega
  have hq : 0 < CH.ceilDiv n s := by
    by_contra h
    have hzero : CH.ceilDiv n s = 0 := by omega
    rw [hzero, Nat.zero_mul] at hnq
    omega
  exact ch_of_boundaryRegular hs (hBR _ _ hq hs) hn hnq hloop hdeg

end Compose.Boundary
