import checkpoints.shen_extension.DeleteRepairUnlock

namespace LeanCH.BR.FundedCascade
open Finset BRq2 BRq3
variable (D : CH.Digraph) (V T : Finset ℕ) (e : ℕ → ℕ)

/-- Active vertices for a single fixed terminal set and horizon. -/
def active : ℕ → Finset ℕ
  | 0 => T
  | k+1 => active k ∪ V.filter (fun u => e u < (outN D (active k) u).card)

theorem active_mono {i k : ℕ} (le : i≤k) : active D V T e i ⊆ active D V T e k := by
  induction le with
  | refl => exact fun _ h => h
  | step _ ih => exact ih.trans subset_union_left

theorem active_sub (tv : T⊆V) (k : ℕ) : active D V T e k ⊆ V := by
  induction k with
  | zero => exact tv
  | succ _ ih => exact union_subset ih (filter_subset _ _)

def cut (C : ℕ → Finset ℕ) : CH.Digraph := fun u v => D u v && decide (v∉C u)

def reaches (E : CH.Digraph) (V T : Finset ℕ) (u k : ℕ) : Prop :=
  ∃p∈T, ∃l≤k, Walk E V u p l

theorem robust (tv : T⊆V) {u k} (act : u∈active D V T e k)
    (C : ℕ → Finset ℕ) (budget : ∀x∈V,(C x).card≤e x) :
    reaches (cut D C) V T u k := by
  induction k generalizing u with
  | zero => exact ⟨u,act,0,le_rfl,.refl _⟩
  | succ k ih =>
    obtain old | new := mem_union.mp act
    · obtain ⟨p,pt,l,lk,path⟩ := ih old
      exact ⟨p,pt,l,by omega,path⟩
    · obtain ⟨uv,rich⟩ := mem_filter.mp new
      obtain ⟨v,hit,keep⟩ : ∃v∈outN D (active D V T e k) u,v∉C u := by
        by_contra! all
        exact (not_lt_of_ge ((card_le_card all).trans (budget u uv))) rich
      obtain ⟨va,edge⟩ := mem_outN.mp hit
      obtain ⟨p,pt,l,lk,path⟩ := ih va
      exact ⟨p,pt,l+1,by omega,.step (active_sub D V T e tv k va) (by simp [cut,edge,keep]) path⟩

/-- Remember each physical row's largest affordable set of active heads. -/
def bill (u : ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | k+1 => if (outN D (active D V T e k) u).card ≤ e u
            then outN D (active D V T e k) u else bill u k

theorem affordable (u K : ℕ) : (bill D V T e u K).card≤e u := by
  induction K with
  | zero => simp [bill]
  | succ k ih => unfold bill; split <;> assumption

private theorem out_mono {A B : Finset ℕ} {u} (h : A⊆B) : outN D A u⊆outN D B u :=
  fun _ he => mem_outN.mpr ⟨h (mem_outN.mp he).1,(mem_outN.mp he).2⟩

theorem billed {u k K} (hk : k<K) (uv : u∈V) (off : u∉active D V T e (k+1)) :
    outN D (active D V T e k) u ⊆ bill D V T e u K := by
  induction K with
  | zero => omega
  | succ K ih =>
    unfold bill
    split
    · exact out_mono D (active_mono D V T e (by omega))
    · rename_i big
      have ne : k≠K := by
        rintro rfl
        exact off (mem_union_right _ (mem_filter.mpr ⟨uv,lt_of_not_ge big⟩))
      exact ih (by omega)

theorem sound_cut {u p l K} (uv : u∈V) (pt : p∈T) (lk : l≤K)
    (path : Walk (cut D (fun x=>bill D V T e x K)) V u p l) :
    u∈active D V T e l := by
  induction path with
  | refl => exact pt
  | @step x y p k yv edge _ ih =>
    have ya := ih yv pt (by omega)
    obtain ⟨native,kept⟩ := Bool.and_eq_true_iff.mp edge
    by_contra off
    exact (of_decide_eq_true kept) (billed D V T e (by omega) uv off (mem_outN.mpr ⟨ya,native⟩))

/-- One budgeted cut works for every starting vertex and every horizon up to K. -/
theorem simultaneous_exact (tv : T⊆V) (K : ℕ) :
    ∃C : ℕ → Finset ℕ, (∀x,(C x).card≤e x) ∧
      ∀u∈V,∀i≤K, (u∈active D V T e i ↔ reaches (cut D C) V T u i) := by
  refine ⟨fun x=>bill D V T e x K,fun x=>affordable D V T e x K,?_⟩
  intro u uv i ik
  refine ⟨fun act=>robust D V T e tv act _ (fun x _=>affordable D V T e x K),?_⟩
  rintro ⟨p,pt,l,li,path⟩
  exact active_mono D V T e li (sound_cut D V T e uv pt (li.trans ik) path)

#print axioms simultaneous_exact
end LeanCH.BR.FundedCascade
