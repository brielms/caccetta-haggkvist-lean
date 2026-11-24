import checkpoints.shen_extension.ReceiverShortcutPrice

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 BRsub JointShortcut

def bankCut (D : CH.Digraph) (F Z : Finset ℕ) : CH.Digraph := fun a c=>
  if c∈F ∧ (∀z∈Z,D a z≠true) then false else D a c

theorem bankCut_sub {D F Z} (u v) (hit : bankCut D F Z u v=true) : D u v=true := by
  unfold bankCut at hit; split at hit <;> simp_all

/-- The common repair preserves every previously certified last-arc
barrier and installs all missing g→b arcs on one graph. -/
theorem common_safe {D V H F Z q b} (free : QFree D V q) (hv : H⊆V)
    (bm : b∈H) (off : b∉F) (zv : Z⊆V) (toB : ∀z∈Z,D z b=true) :
    QFree (install (bankCut D F Z) (F×ˢ{b})) H q := by
  classical
  let K:=bankCut D F Z
  have clear (g) (gm : g∈F) (k) (len : k+1≤q) (w : Walk K H b g k) : False := by
    have sub (x y) (arc : K x y=true) : lastCut D g Z x y=true := by
      unfold lastCut
      split
      next ban =>
        have gone : y∈F ∧ ∀z∈Z,D x z≠true := ⟨ban.1 ▸ gm,ban.2⟩
        change bankCut D F Z x y=true at arc
        rw [bankCut,ite_eq_left gone] at arc
        contradiction
      next => exact bankCut_sub _ _ arc
    exact lastCut_clear free hv bm (fun eq=>off (eq ▸ gm)) zv toB
      (mem_ball.mpr ⟨w.end_mem_or.resolve_left (fun eq=>off (eq ▸ gm)), k,by omega,walk_sub sub w⟩)
  apply ranked_safe (fun _=>0) (fun j jm=>(mem_singleton.mp (mem_product.mp jm).2) ▸ bm)
    (qfree_sub bankCut_sub (free.mono_set hv))
  · intro j jm d le walk
    have ⟨tail,head⟩ := mem_product.mp jm
    rw [mem_singleton.mp head] at walk
    exact clear _ tail _ le walk
  · intro j jm i im _ _ d le walk
    rw [mem_singleton.mp (mem_product.mp jm).2] at walk
    exact clear _ (mem_product.mp im).1 _ (by omega) walk

theorem bankCut_row {D H F Z a} :
    outN (bankCut D F Z) H a=
      if (∀z∈Z,D a z≠true) then outN D H a\F else outN D H a := by
  split
  next off =>
    ext c
    by_cases cm : c∈F
    · have zero : bankCut D F Z a c=false := ite_eq_left ⟨cm,off⟩
      simp [mem_outN,zero,cm]
    · have keep : bankCut D F Z a c=D a c := ite_eq_right (fun h=>cm h.1)
      simp [mem_outN,keep,cm]
  next hit =>
    ext c
    have keep : bankCut D F Z a c=D a c := ite_eq_right (fun h=>hit h.2)
    simp only [mem_outN,keep]

/-- All short rows can share the same fresh head b. Each row that loses
arcs is charged only for its own original heads in F. The strict row b
may be chosen because it never points at one of the short rows. -/
theorem common_repair_false {D V H F Z q t b} (free : QFree D V q) (hv : H⊆V)
    (cut : 1≤q) (size : H.card=q*t+1) (br : Compose.Boundary.BoundaryRegular q t)
    (bm : b∈H) (off : b∉F) (zv : Z⊆V) (toB : ∀z∈Z,D z b=true)
    (fresh : ∀g∈F,D g b≠true)
    (short : ∀g∈F,t≤(outN D H g).card+1 ∧ ∃z∈Z,D g z=true)
    (others : ∀a∈H,a∉F → t≤(outN D H a).card)
    (paid : ∀a∈H,(∀z∈Z,D a z≠true) → t+(outN D H a∩F).card≤(outN D H a).card)
    (strict : t<(outN D H b).card) (protect : Disjoint (outN D H b) F) : False := by
  classical
  let K:=bankCut D F Z
  let E:=install K (F×ˢ{b})
  have old a : outN K H a⊆outN E H a := fun x xm=>
    mem_outN.mpr ⟨(mem_outN.mp xm).1,install_old (mem_outN.mp xm).2⟩
  have budgets a (am : a∈H) : t≤(outN E H a).card := by
    by_cases af : a∈F
    · obtain ⟨near,z,zm,az⟩ := short a af
      have keep : outN K H a=outN D H a := bankCut_row.trans (ite_eq_right (fun p=>p z zm az))
      have new : insert b (outN K H a)⊆outN E H a := insert_subset
        (mem_outN.mpr ⟨bm,install_new (mem_product.mpr ⟨af,mem_singleton_self _⟩)⟩) (old a)
      have notOld : b∉outN K H a := fun m=>fresh a af (bankCut_sub _ _ (mem_outN.mp m).2)
      have bound := card_le_card new
      rw [card_insert_of_notMem notOld,keep] at bound
      omega
    · apply le_trans _ (card_le_card (old a))
      change t≤(outN (bankCut D F Z) H a).card
      rw [bankCut_row]
      split
      next misses =>
        have payments := paid a am misses
        have slots := card_sdiff_add_card_inter (outN D H a) F
        omega
      next => exact others a am af
  have keep : outN K H b=outN D H b := by
    rw [show outN K H b=_ from bankCut_row]
    split
    next => exact Subset.antisymm sdiff_subset (fun _ m=>mem_sdiff.mpr ⟨m,disjoint_left.mp protect m⟩)
    next => rfl
  have hi := card_le_card (old b)
  rw [keep] at hi
  exact WeightedSD.boundary_regular_no_excess cut br (common_safe free hv bm off zv toB)
    size budgets bm (strict.trans_le hi)

#print axioms common_safe
#print axioms common_repair_false
end LeanCH.BR.LabelledCompromiseRecipe
