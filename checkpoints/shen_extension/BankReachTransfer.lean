import checkpoints.shen_extension.LightRowRadius
import checkpoints.shen_extension.SharedLayerBarrier

namespace LeanCH.BR.BankReachTransfer
open Finset BRq2 BRq3 BR45 BRsGen

/-- The size of the outside bank need not equal the cutoff. A single
extra required head inside P∪Q and the size of P determine the radius
in which every starting label of P reaches every target of Q. -/
theorem reaches_bank {D V P Q q k} (free : QFree D V q) (hq : 1≤q)
    (pv : P⊆V) (qv : Q⊆V) (apart : Disjoint P Q)
    (native : ∀v∈V,2≤(outN D V v).card)
    (paid : ∀v∈P,Q.card+1≤(outN D (P∪Q) v).card)
    (small : P.card≤2*q) (time : k≤q) (pressure : P.card≤q+k+1) :
    ∀x∈P,∀y∈Q,∃i,0<i ∧ i≤k+1 ∧ Walk D V x y i := by
  have internal v (vm : v∈P) : 0<(outN D P v).card := by
    have need := paid v vm
    rw [card_outN_union apart] at need
    have lim : (outN D Q v).card≤Q.card := card_le_card outN_subset
    omega
  intro x xm y ym
  obtain ⟨v,near,one⟩ := LocalBallTransfer.reach_light_tight free hq pv xm native internal small time pressure
  obtain ⟨vp,i,length,path⟩ := mem_ball.mp near
  have need := paid v vp
  rw [card_outN_union apart,one] at need
  have full : outN D Q v=Q := eq_of_subset_of_card_le outN_subset (by omega)
  have dest : y∈outN D Q v := full.symm ▸ ym
  exact ⟨i+1,by omega,by omega,(path.mono pv).snoc (qv ym) (mem_outN.mp dest).2⟩

/-- Transfer a reached shell and every later shell, while retaining actual
vertex identities. The starting stem, offset and horizon are arbitrary. -/
theorem shells {D V u w j d} (uv : u∈V)
    (first : ball D V u (j+1)\ball D V u j ⊆ ball D V w d) :
    ∀k,ball D V u (j+1+k)\ball D V u j ⊆ ball D V w (d+k) := by
  intro k
  induction k with
  | zero => simpa using first
  | succ k ih =>
    intro z zm
    obtain ⟨reach,off⟩ := mem_sdiff.mp zm
    by_cases old : z∈ball D V u (j+1+k)
    · exact ball_mono_radius (by omega : d+k≤d+(k+1)) (ih (mem_sdiff.mpr ⟨old,off⟩))
    obtain ⟨y,ym,edge⟩ := ball_succ_pred uv reach old
    have late : y∉ball D V u j := fun earlier=>old (ball_mono_radius (by omega : j+1≤j+1+k)
      (ball_step earlier (ball_subset reach) edge))
    exact ball_step (ih (mem_sdiff.mpr ⟨ym,late⟩)) (ball_subset reach) edge

/-- In addition to all later shells, a marked row retains the labels it
reaches inside the earlier ball. The two contributions are disjoint. -/
theorem count_with_prefix {D V u w j d k} (uv : u∈V) {A : Finset ℕ} (sub : A⊆ball D V u j)
    (inside : A⊆ball D V w (d+k))
    (first : ball D V u (j+1)\ball D V u j ⊆ball D V w d) :
    A.card+((ball D V u (j+1+k)).card-(ball D V u j).card)≤(ball D V w (d+k)).card := by
  let T := ball D V u (j+1+k)\ball D V u j
  have apart : Disjoint A T := disjoint_left.mpr (fun _ a t=>(mem_sdiff.mp t).2 (sub a))
  have cap := card_le_card (union_subset inside (shells uv first k))
  rw [card_union_of_disjoint apart,card_sdiff_of_subset (ball_mono_radius (by omega : j≤j+1+k))] at cap
  exact cap

#print axioms reaches_bank
#print axioms shells
#print axioms count_with_prefix
end LeanCH.BR.BankReachTransfer
