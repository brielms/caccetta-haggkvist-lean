import checkpoints.shen_extension.ReceiverCoverCatalog

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 BRsub JointShortcut

/-- A row may retain its arcs to F when it reaches every proposed head
through Y. The intermediaries may differ at every row and every head. -/
def meetsMenu (D : CH.Digraph) (Y B : Finset ℕ) (a : ℕ) : Prop :=
  ∀b∈B,∃z∈Y,D a z=true ∧ D z b=true
instance {D Y B a} : Decidable (meetsMenu D Y B a) := by unfold meetsMenu; infer_instance

def menuCut (D : CH.Digraph) (F Y B : Finset ℕ) : CH.Digraph := fun a c=>
  if c∈F ∧ ¬meetsMenu D Y B a then false else D a c

theorem menu_sub {D F Y B} (u v) (arc : menuCut D F Y B u v=true) : D u v=true := by
  unfold menuCut at arc; split at arc <;> simp_all

theorem menu_row {D H F Y B a} : outN (menuCut D F Y B) H a=
    if meetsMenu D Y B a then outN D H a else outN D H a\F := by
  split
  next yes =>
    ext c
    have h : menuCut D F Y B a c=D a c := ite_eq_right (fun p=>p.2 yes)
    simp only [mem_outN,h]
  next no =>
    ext c
    by_cases cm : c∈F
    · have off : menuCut D F Y B a c=false := ite_eq_left ⟨cm,no⟩
      simp [mem_outN,off,cm]
    · have keep : menuCut D F Y B a c=D a c := ite_eq_right (fun p=>cm p.1)
      simp [mem_outN,keep,cm]

theorem menu_safe {D V H F Y B q} (free : QFree D V q) (hv : H⊆V)
    (bh : B⊆H) (dis : Disjoint B F) (yv : Y⊆V) :
    QFree (install (menuCut D F Y B) (F×ˢB)) H q := by
  let K:=menuCut D F Y B
  have clear b (bm : b∈B) g (gm : g∈F) (k) (len : k+1≤q) (w : Walk K H b g k) : False := by
    let Z:=inN D Y b
    have ne : b≠g := fun eq=>disjoint_left.mp dis bm (eq ▸ gm)
    have zv : Z⊆V := fun _ zm=>yv (mem_inN.mp zm).1
    have sub u c (arc : K u c=true) : lastCut D g Z u c=true := by
      unfold lastCut
      split
      next test =>
        have bad : ¬meetsMenu D Y B u := by
          intro good
          obtain ⟨z,zy,uz,zb⟩ := good b bm
          exact test.2 z (mem_inN.mpr ⟨zy,zb⟩) uz
        have gone : c∈F ∧ ¬meetsMenu D Y B u := ⟨test.1 ▸ gm,bad⟩
        change menuCut D F Y B u c=true at arc
        rw [menuCut,ite_eq_left gone] at arc
        contradiction
      next => exact menu_sub _ _ arc
    exact lastCut_clear free hv (bh bm) ne zv (fun z zm=>(mem_inN.mp zm).2)
      (mem_ball.mpr ⟨w.end_mem_or.resolve_left (Ne.symm ne),k,by omega,walk_sub sub w⟩)
  apply ranked_safe (fun _=>0) (fun i im=>bh (mem_product.mp im).2)
    (qfree_sub menu_sub (free.mono_set hv))
  · intro i im d cap w
    exact clear _ (mem_product.mp im).2 _ (mem_product.mp im).1 _ cap w
  · intro j jm i im _ _ d cap w
    exact clear _ (mem_product.mp jm).2 _ (mem_product.mp im).1 _ (by omega) w

/-- Exact row accounting on the common cut. A fresh target may depend on
the short row choosing it. One protected strict row prevents the host. -/
theorem menu_repair_false {D V H F Y B q t} (free : QFree D V q) (hv : H⊆V)
    (cut : 1≤q) (size : H.card=q*t+1) (br : Compose.Boundary.BoundaryRegular q t)
    (bh : B⊆H) (dis : Disjoint B F) (yv : Y⊆V)
    (short : ∀g∈F,t≤(outN D H g).card+1 ∧ meetsMenu D Y B g ∧ ∃b∈B,D g b≠true)
    (others : ∀a∈H,a∉F → t≤(outN D H a).card)
    (paid : ∀a∈H,¬meetsMenu D Y B a → t+(outN D H a∩F).card≤(outN D H a).card)
    (strict : ∃b∈H,t<(outN D H b).card ∧ Disjoint (outN D H b) F) : False := by
  classical
  let K:=menuCut D F Y B
  let E:=install K (F×ˢB)
  have old a : outN K H a⊆outN E H a := fun _ m=>mem_outN.mpr ⟨(mem_outN.mp m).1,install_old (mem_outN.mp m).2⟩
  have rows a (am : a∈H) : t≤(outN E H a).card := by
    by_cases af : a∈F
    · obtain ⟨near,good,b,bm,fresh⟩ := short a af
      have keep : outN K H a=outN D H a := menu_row.trans (ite_eq_left good)
      have new : insert b (outN K H a)⊆outN E H a := insert_subset
        (mem_outN.mpr ⟨bh bm,install_new (mem_product.mpr ⟨af,bm⟩)⟩) (old a)
      have notOld : b∉outN K H a := fun m=>fresh (menu_sub _ _ (mem_outN.mp m).2)
      have budget := card_le_card new
      rw [card_insert_of_notMem notOld,keep] at budget
      omega
    · apply le_trans _ (card_le_card (old a))
      change t≤(outN (menuCut D F Y B) H a).card
      rw [menu_row]
      split
      next => exact others a am af
      next bad =>
        have := paid a am bad
        have := card_sdiff_add_card_inter (outN D H a) F
        omega
  obtain ⟨b,bm,hi,protect⟩ := strict
  have keep : outN K H b=outN D H b := by
    rw [show outN K H b=_ from menu_row]
    split
    next => rfl
    next => exact Subset.antisymm sdiff_subset (fun _ m=>mem_sdiff.mpr ⟨m,disjoint_left.mp protect m⟩)
  have more := card_le_card (old b)
  rw [keep] at more
  exact WeightedSD.boundary_regular_no_excess cut br (menu_safe free hv bh dis yv) size rows bm (hi.trans_le more)

#print axioms menu_safe
#print axioms menu_repair_false
end LeanCH.BR.LabelledCompromiseRecipe
