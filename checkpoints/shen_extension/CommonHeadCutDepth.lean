import checkpoints.shen_extension.CommonHeadLastCut

namespace LeanCH.BR.CommonHeadCutDepth
open Finset BRq2 BRq3 BR45 FundedCascade BypassRepair BypassBankReplay JointShortcut CommonHeadLastCut
open scoped Classical

/-- Only keep arcs appearing on an original exact return for the chosen
target of an actual short row. Different retained arcs may have different witnesses. -/
noncomputable def routes (D : CH.Digraph) (U S : Finset ℕ) (q : ℕ) (f : ℕ → ℕ) : CH.Digraph := by
  classical
  exact fun a b => decide (D a b=true ∧ ∃ u∈S,∃ i j : ℕ, i+1+j=q-1 ∧
    Walk D U (f u) a i ∧ Walk D U b u j)

private theorem native {D U S q f} (a b) (arc : routes D U S q f a b=true) : D a b=true :=
  (of_decide_eq_true arc).1

private theorem kept_walk {D U S q f C u a i k} (us : u∈S) (pre : Walk D U (f u) a i)
    (total : i+k=q-1) (rest : Walk (cut D C) U a u k) :
    Walk (cut (routes D U S q f) C) U a u k := by
  induction k generalizing a i with
  | zero => cases rest; exact .refl _
  | succ k ih =>
    cases rest with
    | step bv edge next =>
      obtain ⟨arc,kept⟩ := Bool.and_eq_true_iff.mp edge
      refine .step bv (Bool.and_eq_true_iff.mpr ⟨?_,kept⟩) (ih (pre.snoc bv arc) (by omega) next)
      exact decide_eq_true ⟨arc,u,us,i,k,by omega,pre,walk_sub cut_sub next⟩

/-- A binary tree of walks of a prescribed depth, allowing vertices on
different branches to coincide. Every pair of siblings has distinct labels. -/
def Branches (E : CH.Digraph) (U S : Finset ℕ) : ℕ → ℕ → Prop
  | 0, x => x∈S
  | k+1, x => ∃ a∈U,∃ b∈U,a≠b ∧ E x a=true ∧ E x b=true ∧
      Branches E U S k a ∧ Branches E U S k b

/-- Every assignment on a two-vertex bank with shared fresh targets forces
a fully branching return relation, all the way back to one assigned head. -/
theorem full_depth {D V q s p h} (free : QFree D V q) (hq : 3≤q) (reg : OutEq s D V)
    (hs : 2≤s) (pv : p∈V) (hv : h∈V) (ph : p≠h) (bank : Eligible V {p,h} q (s-1))
    (none : NoHost q (s-1)) (f : ℕ → ℕ)
    (choose : ∀ u∈jointParents D V p h,f u∈heads D V p h ∧ D u (f u)≠true) :
    let U := V \ {p,h}
    let S := jointParents D V p h
    ∃ u∈S,Branches (routes D U S q f) U S (q-1) (f u) := by
  classical
  let U := V \ {p,h}
  let S := jointParents D V p h
  let E := routes D U S q f
  let e := spare D U (s-1)
  let C := fun x => FundedCascade.bill E U S e x (q-1)
  have budget (x) (_ : x∈U) : (C x).card≤e x := affordable E U S e x (q-1)
  obtain ⟨u,us,back⟩ := chosen_return free hq reg hs pv hv ph bank none f choose budget
  have zU : f u∈U := common_head_retained free (by omega) pv hv (choose u us).1
  have zV := (mem_sdiff.mp zU).1
  have parents := mem_inter.mp (choose u us).1
  have sU : S⊆U := by
    intro r rs
    obtain ⟨rv,rp,rh⟩ := parent_data rs
    have a : r≠p := fun eq => loopfree free (by omega) pv (eq ▸ rp)
    have b : r≠h := fun eq => loopfree free (by omega) hv (eq ▸ rh)
    exact mem_sdiff.mpr ⟨rv,by simp [a,b]⟩
  have lift : Walk (cut E C) U (f u) u (q-1) := kept_walk us (.refl _) (by omega) back
  have root := sound_cut E U S e zU us (le_refl (q-1)) lift
  have deep (k) : ∀ a∈U,∀ i, i+k=q-1 → Walk D U (f u) a i →
      a∈active E U S e k → Branches E U S k a := by
    induction k with
    | zero => intro a _ _ _ _ hit; exact hit
    | succ k ih =>
      intro a au i length past hit
      obtain old | fork := mem_union.mp hit
      · obtain ⟨r,rs,l,lk,short⟩ := robust E U S e sU old C budget
        have nxt : Walk D U a r l := walk_sub native (walk_sub cut_sub short)
        have bad : Walk D V p p (((i+l)+1)+1) := .step zV (mem_outN.mp parents.1).2
          (((past.append nxt).mono sdiff_subset).snoc pv (parent_data rs).2.1)
        exact False.elim (free p _ (by omega) (by omega) bad)
      · obtain ⟨_,lots⟩ := mem_filter.mp fork
        have miss (b) (bv : b∈V) (bz : D b (f u)=true) : D a b≠true := by
          intro ab
          have w : Walk D V b b ((i+1)+1) := .step zV bz ((past.mono sdiff_subset).snoc bv ab)
          exact free _ _ (by omega) (by omega) w
        have ap := miss p pv (mem_outN.mp parents.1).2
        have ah := miss h hv (mem_outN.mp parents.2).2
        have allOut : outN D U a=outN D V a := by
          ext x
          simp only [U,mem_outN,mem_sdiff,mem_insert,mem_singleton]
          grind
        have one : 1≤e a := by
          change 1≤(outN D U a).card-(s-1)
          rw [allOut,reg _ (mem_sdiff.mp au).1]
          omega
        obtain ⟨v,vm,w,wm,ne⟩ := one_lt_card.mp (lt_of_le_of_lt one lots)
        obtain ⟨va,av⟩ := mem_outN.mp vm
        obtain ⟨wa,aw⟩ := mem_outN.mp wm
        have vu := active_sub E U S e sU k va
        have wu := active_sub E U S e sU k wa
        exact ⟨v,vu,w,wu,ne,av,aw,ih v vu (i+1) (by omega) (past.snoc vu (native _ _ av)) va,
          ih w wu (i+1) (by omega) (past.snoc wu (native _ _ aw)) wa⟩
  exact ⟨u,us,deep (q-1) (f u) zU 0 (by omega) (.refl _) root⟩

/-- Distinct walks counted by the ordered list of labels after the start. -/
def words (E : CH.Digraph) (U S : Finset ℕ) : ℕ → ℕ → Finset (List ℕ)
  | 0, x => if x∈S then {[]} else ∅
  | k+1, x => (outN E U x).biUnion (fun a => (words E U S k a).image (List.cons a))

theorem word_count {E U S k x} (tree : Branches E U S k x) : 2^k ≤ (words E U S k x).card := by
  induction k generalizing x with
  | zero =>
    change x∈S at tree
    simp [words,tree]
  | succ k ih =>
    obtain ⟨a,au,b,bu,ne,xa,xb,left,right⟩ := tree
    let A := (words E U S k a).image (List.cons a)
    let B := (words E U S k b).image (List.cons b)
    have separate : Disjoint A B := by
      apply disjoint_left.mpr
      intro l la lb
      obtain ⟨v,_,rfl⟩ := mem_image.mp la
      obtain ⟨w,_,eq⟩ := mem_image.mp lb
      exact ne (List.cons.inj eq).1.symm
    have sub : A ∪ B ⊆ words E U S (k+1) x := by
      intro l lm
      rcases mem_union.mp lm with la|lb
      · exact mem_biUnion.mpr ⟨a,mem_outN.mpr ⟨au,xa⟩,la⟩
      · exact mem_biUnion.mpr ⟨b,mem_outN.mpr ⟨bu,xb⟩,lb⟩
    have cnt := card_le_card sub
    rw [card_union_of_disjoint separate] at cnt
    have ca : A.card=(words E U S k a).card := card_image_of_injective _ (fun _ _ eq => (List.cons.inj eq).2)
    have cb : B.card=(words E U S k b).card := card_image_of_injective _ (fun _ _ eq => (List.cons.inj eq).2)
    rw [ca,cb] at cnt
    have first := ih left
    have second := ih right
    rw [pow_succ]
    omega

#print axioms word_count

#print axioms full_depth
end LeanCH.BR.CommonHeadCutDepth

