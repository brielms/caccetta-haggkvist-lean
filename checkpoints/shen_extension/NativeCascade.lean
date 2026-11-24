import checkpoints.shen_extension.FundedCascade

namespace LeanCH.BR.FundedCascade
open Finset BRq2 BRq3
variable {D : CH.Digraph} {V : Finset ℕ} {h q s : ℕ}

/-- All rows that need a replacement after deleting h. -/
def parents (D : CH.Digraph) (V : Finset ℕ) (h s : ℕ) :=
  V.filter (fun p => D p h = true ∧ (outN D V p).card = s)

def spare (D : CH.Digraph) (V : Finset ℕ) (s u : ℕ) := (outN D V u).card - s

private def protect (D : CH.Digraph) (h : ℕ) (C : ℕ → Finset ℕ) (u : ℕ) :=
  if D u h = true then ∅ else C u

/-- Restoring all cuts at parents of h creates no new short return from a head of h. -/
private theorem protected_walk {C : ℕ → Finset ℕ} {x p k l : ℕ} (free : QFree D V q)
    (hv : h∈V) (approach : Walk D V h x k) (lim : k+l≤q)
    (path : Walk (cut D (protect D h C)) V x p l) :
    Walk (cut D C) V x p l := by
  induction path generalizing k with
  | refl => exact .refl _
  | @step x y p l yv arc _ ih =>
    have no : ¬ D x h = true := fun back =>
      free h (k+1) (by omega) (by omega) (approach.snoc hv back)
    have native := (Bool.and_eq_true_iff.mp arc).1
    have old : cut D C x y = true := by simpa [cut,protect,no] using arc
    exact .step yv old (ih (approach.snoc yv native) (by omega))

/-- A tight parent always misses some head of h, including when h has minimum degree. -/
theorem missing_head (free : QFree D V q) (hq : 1≤q) (hv : h∈V)
    (deg : s≤(outN D V h).card) {p} (pt : p∈parents D V h s) :
    ∃w∈outN D V h, D p w ≠ true := by
  obtain ⟨_,ph,pc⟩ := mem_filter.mp pt
  have hh := loopfree free hq hv
  by_contra! covers
  have sub : outN D V h ⊆ (outN D V p).erase h := by
    intro w wh
    obtain ⟨wv,hw⟩ := mem_outN.mp wh
    exact mem_erase.mpr ⟨fun eq => hh (eq ▸ hw),mem_outN.mpr ⟨wv,covers w wh⟩⟩
  have bound := card_le_card sub
  rw [card_erase_of_mem (mem_outN.mpr ⟨hv,ph⟩),pc] at bound
  have pos := card_pos.mpr (show (outN D V p).Nonempty from ⟨h,mem_outN.mpr ⟨hv,ph⟩⟩)
  omega

/-- Deletion minimality forces one tight parent all of whose missing shortcut heads
are robustly active towards the entire tight-parent set. -/
theorem forced_parent (free : QFree D V q) (hq : 1≤q) (hv : h∈V)
    (deg : ∀u∈V, s≤(outN D V u).card)
    (minimal : ∀E : CH.Digraph, QFree E (V.erase h) q →
      ¬ (∀u∈V.erase h, s≤(outN E (V.erase h) u).card)) :
    ∃p∈parents D V h s, ∀w∈outN D V h, D p w ≠ true →
      w∈active D V (parents D V h s) (spare D V s) (q-1) := by
  classical
  let T := parents D V h s
  let e := spare D V s
  let A := active D V T e (q-1)
  let C := fun x => bill D V T e x (q-1)
  let E := cut D (protect D h C)
  let S := fun u => (outN D V h).filter (fun w => D u w ≠ true ∧ w∉A)
  let F := DeleteRepair.repair E T S
  by_contra! none
  have choices : ∀u∈T, (S u).Nonempty := by
    intro u ut
    obtain ⟨w,wh,miss,off⟩ := none u ut
    exact ⟨w,mem_filter.mpr ⟨wh,miss,off⟩⟩
  have ef : QFree E V q := by
    intro u l lo hi path
    exact free u l lo hi (walk_sub (fun _ _ edge => (Bool.and_eq_true_iff.mp edge).1) path)
  have ff : QFree F V q := by
    apply DeleteRepair.repair_qfree ef
    intro u ut w ws p pt l lim path
    obtain ⟨wh,_,off⟩ := mem_filter.mp ws
    obtain ⟨wv,hw⟩ := mem_outN.mp wh
    have pre : Walk D V h w 1 := .step wv hw (.refl _)
    have orig := protected_walk free hv pre (by omega) path
    exact off (active_mono D V T e (by omega : l≤q-1) (sound_cut D V T e wv pt (by omega : l≤q-1) orig))
  apply minimal F (fun u l lo hi path => ff u l lo hi (path.mono (erase_subset h V)))
  intro u ur
  obtain ⟨_,uv⟩ := mem_erase.mp ur
  let H := outN D V u
  let J := outN F (V.erase h) u
  have du : s≤H.card := deg u uv
  by_cases ph : D u h = true
  · have hm : h∈H := mem_outN.mpr ⟨hv,ph⟩
    have sub : H.erase h ⊆ J := by
      intro y ym
      obtain ⟨ne,yh⟩ := mem_erase.mp ym
      obtain ⟨yv,uy⟩ := mem_outN.mp yh
      exact mem_outN.mpr ⟨mem_erase.mpr ⟨ne,yv⟩,DeleteRepair.repair_old (by simp [E,cut,protect,ph,uy])⟩
    by_cases tight : H.card=s
    · have ut : u∈T := mem_filter.mpr ⟨uv,ph,tight⟩
      obtain ⟨w,ws⟩ := choices u ut
      obtain ⟨wh,miss,_⟩ := mem_filter.mp ws
      obtain ⟨wv,hw⟩ := mem_outN.mp wh
      have ne : w≠h := fun eq => loopfree free hq hv (eq ▸ hw)
      have wj : w∈J := mem_outN.mpr ⟨mem_erase.mpr ⟨ne,wv⟩,DeleteRepair.repair_new ut ws⟩
      have no : w∉H.erase h := fun mem => miss (mem_outN.mp (mem_erase.mp mem).2).2
      have b := card_le_card (insert_subset wj sub)
      rw [card_insert_of_notMem no,card_erase_of_mem hm] at b
      exact show s≤J.card by omega
    · have b := card_le_card sub
      rw [card_erase_of_mem hm] at b
      exact show s≤J.card by omega
  · have sub : H \ C u ⊆ J := by
      intro y yes
      obtain ⟨yh,keep⟩ := mem_sdiff.mp yes
      obtain ⟨yv,uy⟩ := mem_outN.mp yh
      have ne : y≠h := fun eq => ph (eq ▸ uy)
      exact mem_outN.mpr ⟨mem_erase.mpr ⟨ne,yv⟩,DeleteRepair.repair_old (by simp [E,cut,protect,ph,uy,keep])⟩
    have split : H⊆(H \ C u) ∪ C u := by
      intro y yh
      by_cases yc : y∈C u
      · exact mem_union_right _ yc
      · exact mem_union_left _ (mem_sdiff.mpr ⟨yh,yc⟩)
    have b := (card_le_card split).trans (card_union_le _ _)
    have a : (C u).card≤H.card-s := affordable D V T e u (q-1)
    have j := card_le_card sub
    exact show s≤J.card by omega

/-- Early activity would close the return through h within the forbidden cutoff. -/
theorem head_inactive_early (free : QFree D V q) (hv : h∈V)
    {w k} (wh : w∈outN D V h) (early : k+2≤q) :
    w∉active D V (parents D V h s) (spare D V s) k := by
  intro act
  obtain ⟨wv,hw⟩ := mem_outN.mp wh
  have tv : parents D V h s⊆V := filter_subset _ _
  obtain ⟨p,pt,l,lk,path⟩ := robust D V _ _ tv act (fun _=>∅) (by simp)
  have native : Walk D V w p l := walk_sub (fun _ _ edge => (Bool.and_eq_true_iff.mp edge).1) path
  have ph := (mem_filter.mp pt).2.1
  have closed := (Walk.step wv hw native).snoc hv ph
  exact free h ((l+1)+1) (by omega) (by omega) closed

/-- Every missing shortcut in the forced row has more independently labelled first hops than
the head can cut, with all those hops active towards one fixed physical parent bank. -/
theorem forced_branching (free : QFree D V q) (hq : 2≤q) (hv : h∈V)
    (deg : ∀u∈V, s≤(outN D V u).card)
    (minimal : ∀E : CH.Digraph, QFree E (V.erase h) q →
      ¬ (∀u∈V.erase h, s≤(outN E (V.erase h) u).card)) :
    ∃p∈parents D V h s, (∃w∈outN D V h, D p w ≠ true) ∧
      ∀w∈outN D V h, D p w ≠ true → spare D V s w <
        (outN D (active D V (parents D V h s) (spare D V s) (q-2)) w).card := by
  obtain ⟨p,pt,all⟩ := forced_parent free (by omega) hv deg minimal
  refine ⟨p,pt,missing_head free (by omega) hv (deg h hv) pt,?_⟩
  intro w wh miss
  have hit := all w wh miss
  rw [show q-1=(q-2)+1 by omega] at hit
  obtain old | fresh := mem_union.mp hit
  · exact False.elim (head_inactive_early free hv wh (by omega) old)
  · exact (mem_filter.mp fresh).2

#print axioms forced_branching

#print axioms missing_head
#print axioms forced_parent
end LeanCH.BR.FundedCascade
