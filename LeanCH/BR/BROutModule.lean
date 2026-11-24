import LeanCH.BR.BRsubM

/-! Saturation upgrades any out-module to a full module, at every cutoff. -/
namespace LeanCH.BR.BRsub
open BRq2 BRq3 BR45

def OutUniform (D : CH.Digraph) (V M : Finset ℕ) : Prop :=
  ∀ x ∈ M, ∀ y ∈ M, ∀ z ∈ V, z ∉ M → D x z = D y z

def InUniform (D : CH.Digraph) (V M : Finset ℕ) : Prop :=
  ∀ x ∈ M, ∀ y ∈ M, ∀ z ∈ V, z ∉ M → D z x = D z y

theorem outUniform_incoming_transfer {D : CH.Digraph} {V M : Finset ℕ} {q : ℕ}
    (hf : QFree D V q) (hsat : Sat q D V) (hMV : M ⊆ V)
    (hout : OutUniform D V M) {x y p : ℕ} (hx : x ∈ M) (hy : y ∈ M)
    (hpV : p ∈ V) (hpM : p ∉ M) (hpx : D p x = true) : D p y = true := by
  classical
  by_contra hpy
  let Y := outN D V x \ M
  have hO : ∀ m ∈ M, ∀ z ∈ V, D m z = true → z ∈ M ∨ z ∈ Y := by
    intro m hm z hz hmz
    by_cases hzM : z ∈ M
    · exact Or.inl hzM
    · right
      apply Finset.mem_sdiff.mpr
      refine ⟨mem_outN.mpr ⟨hz, ?_⟩, hzM⟩
      rw [← hout m hm x hx z hz hzM]
      exact hmz
  have hreach := hsat y (hMV hy) p hpV hpy
  rcases ball_sub_MY hMV hO hy (q - 1) p hreach with hp | ⟨z, hz, j, hj, hpz⟩
  · exact hpM hp
  · obtain ⟨hzout, hzM⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨hzV, hxz⟩ := mem_outN.mp hzout
    have hpball := ball_trans (ball_of_adj hzV hxz) hpz
    exact no_back_arc hf (hMV hx) hpball (by omega) hpx

theorem outUniform_inUniform {D : CH.Digraph} {V M : Finset ℕ} {q : ℕ}
    (hf : QFree D V q) (hsat : Sat q D V) (hMV : M ⊆ V)
    (hout : OutUniform D V M) : InUniform D V M := by
  intro x hx y hy p hpV hpM
  apply Bool.eq_iff_iff.mpr
  exact ⟨outUniform_incoming_transfer hf hsat hMV hout hx hy hpV hpM,
    outUniform_incoming_transfer hf hsat hMV hout hy hx hpV hpM⟩

end LeanCH.BR.BRsub
