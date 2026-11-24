
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSixQ5Floors_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5BankPacking_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5EndpointAssembly_20261121

namespace LeanCH.BR.DotDegreeSix
open Finset BRq2 BRq3 BR45 BRsGen DotDegreeSevenLow
set_option maxHeartbeats 1000000

theorem third_parent {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hu : u∈V) (P : SixPrefix D V u) {x : ℕ} (hx : x∈P.T) :
    ∃ b∈P.B, D b x=true := by
  have xx := hx
  rw [P.t_eq] at xx
  obtain ⟨_,k,k3,w⟩ := mem_ball.mp (mem_sdiff.mp xx).1
  have ek : k=3 := by
    by_contra n
    exact (mem_sdiff.mp xx).2 (mem_ball.mpr ⟨P.tV hx,k,by omega,w⟩)
  subst k
  obtain ⟨b,p,_,e⟩ := w.unsnoc
  have bV : b∈V := (p.end_mem_or).elim (fun h => h.symm ▸ hu) id
  have bb : b∈P.B := by
    rw [P.b_eq]
    refine mem_sdiff.mpr ⟨mem_ball.mpr ⟨bV,2,by decide,p⟩,?_⟩
    intro h
    exact (mem_sdiff.mp xx).2 (ball_step h (P.tV hx) e)
  exact ⟨b,bb,e⟩

/-- At a small first shell, every cycle row reaches every third-layer
    label in two steps. No fourth-layer count is needed to pay the bank. -/
theorem five_spill_bank_gain {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (ho : OutEq 6 D V) (hu : u∈V)
    (P : SixPrefix D V u) (cb : P.B.card=5) :
    ∀ a∈P.A, 14≤(ball D V a 2).card := by
  obtain ⟨cy,full,ts⟩ := five_spill hf ho P cb
  intro a aa
  let I := ball D P.A a 2
  have ia : I⊆P.A := ball_subset
  have i2 : I⊆ball D V a 2 := by
    intro v hv
    obtain ⟨va,k,k2,w⟩ := mem_ball.mp hv
    exact mem_ball.mpr ⟨P.aV va,k,k2,w.mono P.aV⟩
  have b1 (b) (bb : b∈P.B) : b∈ball D V a 1 :=
    ball_of_adj (P.bV bb) (full a aa b bb)
  have b2 : P.B⊆ball D V a 2 := fun b bb => ball_mono_radius (by decide : 1≤2) (b1 b bb)
  have t2 : P.T⊆ball D V a 2 := by
    intro t ht
    obtain ⟨b,bb,bt⟩ := third_parent hu P ht
    exact ball_step (b1 b bb) (P.tV ht) bt
  have low : 3≤I.card := ball_one_growth (hf.mono_set P.aV) (fun v hv => (cy v hv).ge) aa 2 (by decide)
  have num := card_le_card (union_subset (union_subset i2 b2) t2)
  rw [card_union_of_disjoint (P.at'.mono_left (union_subset_union ia (Subset.refl _))),
    card_union_of_disjoint (P.ab.mono_left ia),cb] at num
  omega

/-- Roots sharing the same complete first layer have no reach in
    either direction at any positive allowed length. -/
theorem same_heads_no_reach {D : CH.Digraph} {V : Finset ℕ} {u v q k : ℕ}
    (hf : QFree D V q) (ne : u≠v) (hk : k≤q)
    (same : outN D V u=outN D V v) : v∉ball D V u k := by
  intro h
  obtain ⟨_,i,ik,w⟩ := mem_ball.mp h
  cases w with
  | refl => exact ne rfl
  | @step u x v j xv ux tail =>
    have vx := (mem_outN.mp (same ▸ (mem_outN.mpr ⟨xv,ux⟩ : x∈outN D V u))).2
    have vv := (mem_ball.mp h).1
    exact hf x (j+1) (by omega) (by omega) (tail.snoc xv vx)

/-- The common-cycle labels of any two short roots either agree or are disjoint. -/
theorem first_banks_equal_or_disjoint {D : CH.Digraph} {V : Finset ℕ} {u v : ℕ}
    (hf : QFree D V 5) (ho : OutEq 6 D V)
    (P : SixPrefix D V u) (Q : SixPrefix D V v)
    (pb : P.B.card=5) (qb : Q.B.card=5) :
    Disjoint P.A Q.A ∨ P.A=Q.A := by
  obtain ⟨pc,pfull,_⟩ := five_spill hf ho P pb
  obtain ⟨qc,qfull,_⟩ := five_spill hf ho Q qb
  exact spill_banks_disjoint_or_equal hf P.aV Q.aV P.ca Q.ca pc qc P.first Q.first pfull qfull

#print axioms five_spill_bank_gain
#print axioms same_heads_no_reach
#print axioms first_banks_equal_or_disjoint
end LeanCH.BR.DotDegreeSix

