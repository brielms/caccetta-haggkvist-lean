import checkpoints.shen_extension.PunctureFrontier
import LeanCH.BR.BRCycleReturn

namespace LeanCH.BR.Closure.CycleSquareTensor
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor

/-- Four labelled vertices controlling a replacement of a two-edge path. -/
structure Shift (D : CH.Digraph) (M N : Finset ℕ) (a u v b : ℕ) : Prop where
  aM : a∈M
  uM : u∈M
  bM : b∈M
  exterior : v∉M
  before₁ : D a u=true
  before₂ : D u b=true
  after₁ : D a v=true
  after₂ : D v b=true
  move : D u v=true
  labels : N=insert v (M.erase u)

/-- A receiver fed by two cycle vertices and pointing back to the cycle
has a unique target and exactly its two consecutive predecessors as parents. -/
theorem replacement {D W M q v b} (hq : 2≤q) (safe : QFree D W q) (c : Cycle D W q M)
    (vw : v∈W\M) (rich : 2≤(inN D M v).card) (bm : b∈M) (vb : D v b=true) :
    ∃a u N, Shift D M N a u v b ∧ Cycle D W q N ∧
      inN D M v={a,u} ∧ outN D M v={b} := by
  classical
  have get (x) (xm : x∈M) : ∃y∈M,D y x=true := by
    have one : (inN D M x).card=1 := c.incoming x xm
    obtain ⟨y,hy⟩ := card_pos.mp (by omega : 0<(inN D M x).card)
    exact ⟨y,mem_inN.mp hy⟩
  obtain ⟨u,um,ub⟩ := get b bm
  obtain ⟨a,am,au⟩ := get u um
  have anu : a≠u := fun e => loopfree safe (by omega) (c.sub um) (e ▸ au)
  have bnu : b≠u := fun e => loopfree safe (by omega) (c.sub um) (e ▸ ub)
  let F := M\ball D M b (q-2)
  have cap : F.card≤2 := by
    have size := c.size
    have grown := ball_one_growth (safe.mono_set c.sub) (fun x hx => (c.heads x hx).ge) bm (q-2) (by omega)
    have part := card_sdiff_add_card_eq_card (ball_subset (D:=D) (W:=M) (u:=b) (k:=q-2))
    dsimp [F]
    omega
  have uf : u∈F := by
    refine mem_sdiff.mpr ⟨um,?_⟩
    rintro near
    obtain ⟨_,k,le,p⟩ := mem_ball.mp near
    exact safe b (k+1) (by omega) (by omega) ((p.mono c.sub).snoc (c.sub bm) ub)
  have af : a∈F := by
    refine mem_sdiff.mpr ⟨am,?_⟩
    rintro near
    obtain ⟨_,k,le,p⟩ := mem_ball.mp near
    exact safe b (k+1+1) (by omega) (by omega) (((p.mono c.sub).snoc (c.sub um) au).snoc (c.sub bm) ub)
  have pp : inN D M v⊆F := by
    intro p pc
    refine mem_sdiff.mpr ⟨(mem_inN.mp pc).1,?_⟩
    rintro near
    obtain ⟨_,k,le,path⟩ := mem_ball.mp near
    exact safe v (k+1+1) (by omega) (by omega)
      (.step (c.sub bm) vb ((path.mono c.sub).snoc (mem_sdiff.mp vw).1 (mem_inN.mp pc).2))
  have ef := eq_of_subset_of_card_le pp (cap.trans rich)
  have pair : ({a,u}:Finset ℕ)=F := eq_of_subset_of_card_le (insert_subset af (singleton_subset_iff.mpr uf))
    (by simpa [anu] using cap)
  have parents := ef.trans pair.symm
  have av := (mem_inN.mp (show a∈inN D M v from ef.symm ▸ af)).2
  have uv := (mem_inN.mp (show u∈inN D M v from ef.symm ▸ uf)).2
  have target : {b}⊆outN D M v := singleton_subset_iff.mpr (mem_outN.mpr ⟨bm,vb⟩)
  have lim := BRsub.cycle_two_sided_contact_cap hq safe c.sub c.size c.heads (mem_sdiff.mp vw).1
    (card_pos.mp (by omega)) ⟨b,mem_outN.mpr ⟨bm,vb⟩⟩
  have only := eq_of_subset_of_card_le target (by simp; omega)
  let N := insert v (M.erase u)
  have nv : N⊆W := insert_subset (mem_sdiff.mp vw).1 ((erase_subset _ _).trans c.sub)
  have sz : N.card=q+1 := by
    have ne : v∉M.erase u := fun h => (mem_sdiff.mp vw).2 (mem_of_mem_erase h)
    rw [show N=insert v (M.erase u) from rfl,card_insert_of_notMem ne,card_erase_add_one um,c.size]
  have degree (x) (xn : x∈N) : 1≤(outN D N x).card := by
    rcases mem_insert.mp xn with rfl | xe
    · exact card_pos.mpr ⟨b,mem_outN.mpr ⟨mem_insert_of_mem (mem_erase.mpr ⟨bnu,bm⟩),vb⟩⟩
    obtain ⟨y,hy⟩ := card_pos.mp (by rw [c.heads x (mem_of_mem_erase xe)]; decide : 0<(outN D M x).card)
    obtain ⟨ym,xy⟩ := mem_outN.mp hy
    by_cases yu : y=u
    · subst y
      have one : (inN D M u).card=1 := c.incoming u um
      have xa := card_le_one.mp one.le x (mem_inN.mpr ⟨mem_of_mem_erase xe,xy⟩) a (mem_inN.mpr ⟨am,au⟩)
      exact card_pos.mpr ⟨v,mem_outN.mpr ⟨mem_insert_self _ _,xa ▸ av⟩⟩
    · exact card_pos.mpr ⟨y,mem_outN.mpr ⟨mem_insert_of_mem (mem_erase.mpr ⟨yu,ym⟩),xy⟩⟩
  have reg := dt_reg (by omega : 1≤q) (ball_q_one q (by omega)) (safe.mono_set nv) degree (by simpa using sz)
  exact ⟨a,u,N,⟨am,um,bm,(mem_sdiff.mp vw).2,au,ub,av,vb,uv,rfl⟩,⟨nv,sz,reg.1,reg.2⟩,parents,only.symm⟩

#print axioms replacement
end LeanCH.BR.Closure.CycleSquareTensor
