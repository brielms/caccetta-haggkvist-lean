import checkpoints.shen_extension.DotTwoPassShellTransport_20261117
import Mathlib.Order.Interval.Finset.Nat

namespace LeanCH.BR.ShenContainerTransfer
open BRq2 BRq3 BR45 ShenFirstStrip
open Classical

private theorem segment {D : CH.Digraph} {V : Finset ℕ} {m : ℕ} {f : ℕ → ℕ}
    (edge : ∀ i, i<m → f (i+1)∈V ∧ D (f i) (f (i+1))=true) (i l : ℕ) (h : i+l≤m) :
    Walk D V (f i) (f (i+l)) l := by
  induction l with
  | zero => simpa using (Walk.refl (D:=D) (W:=V) (f i))
  | succ l ih =>
    obtain ⟨hv,he⟩ := edge (i+l) (by omega)
    exact (ih (by omega)).snoc hv he

/-- The actual number of omissions at the target bounds the length of every
source walk of length at most k, provided its final predecessors lie in the
source container and their return budget fits the cutoff. -/
theorem walk_length_le_target_omissions {D : CH.Digraph} {V K : Finset ℕ} {q i j x y m e : ℕ}
    (hf : QFree D V q) (hx : x∈V) (hK : ball D V x i ⊆ K)
    (hm : m≤i) (hmq : m≤q) (w : Walk D V x y m) (hreturn : j+e+1≤q)
    (hmiss : (K \ ball D V y j).card≤e) : m≤e := by
  by_contra! hlong
  obtain ⟨f,hx0,hyM,edge⟩ := w.toFun
  let I := Finset.Ico (m-(e+1)) m
  have bounds {i} (hi : i∈I) : m-(e+1)≤i ∧ i<m := Finset.mem_Ico.mp hi
  have diff (i j : ℕ) (hlt : i<j) (hj : j≤m) : f i≠f j := by
    intro he
    have h := segment edge i (j-i) (by omega)
    rw [show i+(j-i)=j by omega,← he] at h
    exact hf _ (j-i) (by omega) (by omega) h
  have inj : Set.InjOn f (I : Set ℕ) := by
    intro i hi j hj he
    rcases lt_trichotomy i j with h|h|h
    · exact (diff i j h (bounds hj).2.le he).elim
    · exact h
    · exact (diff j i h (bounds hi).2.le he.symm).elim
  have sub : I.image f ⊆ K \ ball D V y j := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hlo,hhi⟩ := bounds hi
    have wp := segment edge 0 i (by omega)
    simp only [Nat.zero_add,hx0] at wp
    have hv : f i∈V := wp.end_mem_or.elim (fun he => he ▸ hx) id
    refine Finset.mem_sdiff.mpr ⟨hK (mem_ball.mpr ⟨hv,i,by omega,wp⟩),?_⟩
    intro hb
    obtain ⟨_,r,hr,wr⟩ := mem_ball.mp hb
    have ws := segment edge i (m-i) (by omega)
    rw [show i+(m-i)=m by omega,hyM] at ws
    exact hf y (r+(m-i)) (by omega) (by omega) (wr.append ws)
  have hc := Finset.card_le_card sub
  rw [Finset.card_image_of_injOn inj] at hc
  have hcard : I.card=e+1 := by dsimp [I]; rw [Nat.card_Ico]; omega
  omega

theorem walk_length_le_omissions {D : CH.Digraph} {V K : Finset ℕ} {q k x y m e : ℕ}
    (hf : QFree D V q) (hx : x∈V) (hK : ball D V x k ⊆ K)
    (hm : m≤k) (w : Walk D V x y m) (hreturn : k+e+1≤q)
    (hmiss : (K \ ball D V y k).card≤e) : m≤e :=
  walk_length_le_target_omissions hf hx hK hm (by omega) w hreturn hmiss

/-- Select e+2 roots. Each reaches another root, and every such step lifts
to at most e original arcs. The finite sink theorem gives the contradiction. -/
theorem container_false {D : CH.Digraph} {V C K : Finset ℕ} {q k e : ℕ}
    (hf : QFree D V q) (hCV : C⊆V) (hCK : C⊆K)
    (hballs : ∀ h∈C, ball D V h k⊆K)
    (hmiss : ∀ h∈C, (K \ ball D V h k).card≤e)
    (hc : e+2≤C.card) (hreturn : k+e+1≤q) (hcycle : e*(e+2)≤q) : False := by
  obtain ⟨A,hAC,hA⟩ := Finset.exists_subset_card_eq hc
  let E : CH.Digraph := fun x y => decide (x≠y ∧ y∈ball D V x k)
  have hfE : QFree E A (e+2) := by
    apply DotTwoPassShellTransport.qfree_of_bounded_arc_lift hf hcycle
    intro x hx y hy hxy
    obtain ⟨hne,hb⟩ := of_decide_eq_true hxy
    obtain ⟨_,m,hm,wm⟩ := mem_ball.mp hb
    refine ⟨m,?_,walk_length_le_omissions hf (hCV (hAC hx)) (hballs x (hAC hx))
      hm wm hreturn (hmiss y (hAC hy)),wm⟩
    cases m with
    | zero => cases wm; exact (hne rfl).elim
    | succ m => omega
  obtain ⟨x,hx,hsink⟩ := exists_sink hfE (Finset.card_pos.mp (by omega)) hA.le
  have sub : A⊆insert x (K \ ball D V x k) := by
    intro y hy
    by_cases he : y=x
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hCK (hAC hy),
        fun hb => hsink y hy (by simp [E,Ne.symm he,hb])⟩))
  have hh := (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)
  have := hmiss x (hAC hx)
  omega

#print axioms walk_length_le_omissions
#print axioms container_false

/-- Run an arbitrary checked degree bound on the compressed bank. The
omissions and the root itself are the only possible missing out-neighbours. -/
theorem container_false_of_order {D : CH.Digraph} {V C K : Finset ℕ} {q k e d m p : ℕ}
    (order : ∀ F W, QFree F W p → (∀ v∈W, d≤(outN F W v).card) → W.Nonempty → m<W.card)
    (hf : QFree D V q) (hCV : C⊆V) (hCK : C⊆K)
    (hballs : ∀ h∈C, ball D V h k⊆K)
    (hmiss : ∀ h∈C, (K \ ball D V h k).card≤e)
    (hc : m≤C.card) (hd : e+1+d≤m) (hreturn : k+e+1≤q) (hcycle : e*p≤q) : False := by
  obtain ⟨A,hAC,hA⟩ := Finset.exists_subset_card_eq hc
  let E : CH.Digraph := fun x y => decide (x≠y ∧ y∈ball D V x k)
  have hfE : QFree E A p := by
    apply DotTwoPassShellTransport.qfree_of_bounded_arc_lift hf hcycle
    intro x hx y hy hxy
    obtain ⟨hne,hb⟩ := of_decide_eq_true hxy
    obtain ⟨_,l,hl,wl⟩ := mem_ball.mp hb
    refine ⟨l,?_,walk_length_le_omissions hf (hCV (hAC hx)) (hballs x (hAC hx))
      hl wl hreturn (hmiss y (hAC hy)),wl⟩
    cases l with
    | zero => cases wl; exact (hne rfl).elim
    | succ l => omega
  have deg (x) (hx : x∈A) : d≤(outN E A x).card := by
    have sub : A⊆insert x ((K \ ball D V x k) ∪ outN E A x) := by
      intro y hy
      by_cases he : y=x
      · exact Finset.mem_insert.mpr (Or.inl he)
      apply Finset.mem_insert_of_mem
      by_cases hb : y∈ball D V x k
      · exact Finset.mem_union_right _ (mem_outN.mpr ⟨hy,by simp [E,Ne.symm he,hb]⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hCK (hAC hy),hb⟩)
    have h1 := (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)
    have h2 := Finset.card_union_le (K \ ball D V x k) (outN E A x)
    have := hmiss x (hAC hx)
    omega
  have := order E A hfE deg (Finset.card_pos.mp (by omega))
  omega

#print axioms container_false_of_order

/-- Six roots with three holes each. The compressed graph on six labels
has minimum outdegree two, hence a closed walk of length at most three. -/
theorem three_omissions_six_roots {D : CH.Digraph} {V C K : Finset ℕ} {q k : ℕ}
    (hf : QFree D V q) (hCV : C⊆V) (hCK : C⊆K)
    (hballs : ∀ h∈C, ball D V h k⊆K)
    (hmiss : ∀ h∈C, (K \ ball D V h k).card≤3)
    (hc : 6≤C.card) (hr : k+4≤q) (hq : 9≤q) : False :=
  container_false_of_order (d:=2) (p:=3)
    (fun _ _ h m ne => corB (by decide) h m ne)
    hf hCV hCK hballs hmiss hc (by decide) hr hq

#print axioms three_omissions_six_roots
end LeanCH.BR.ShenContainerTransfer
