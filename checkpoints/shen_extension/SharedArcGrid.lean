import checkpoints.shen_extension.SharedArcExpansion

namespace LeanCH.BR.Closure.SharedArcGrid
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor

abbrev Color := ℕ → ℕ → Prop

def Switch (D : CH.Digraph) (V : Finset ℕ) (col : Color) : Prop :=
  ∀u∈V,∀v∈V,∀w∈V,D u v=true → D v w=true → ¬(col u v ↔ col v w) → D u w=true

def HasColor (D : CH.Digraph) (C : Finset ℕ) (col : Color) : Prop :=
  ∀u∈C,∀v∈C,D u v=true → col u v

abbrev rev (D : CH.Digraph) : CH.Digraph := fun u v => D v u
abbrev flip (col : Color) : Color := fun u v => col v u
abbrev other (col : Color) : Color := fun u v => ¬col u v

theorem Switch.rev {D V col} (sw : Switch D V col) : Switch (SharedArcGrid.rev D) V (flip col) := by
  intro u uv v vv w wv vu wv' ne
  exact sw w wv v vv u uv wv' vu (fun eq => ne eq.symm)

theorem Switch.other {D V col} (sw : Switch D V col) : Switch D V (SharedArcGrid.other col) := by
  intro u uv v vv w wv e f ne
  exact sw u uv v vv w wv e f (fun eq => ne (not_congr eq))

theorem HasColor.rev {D C col} (c : HasColor D C col) : HasColor (SharedArcGrid.rev D) C (flip col) :=
  fun _ um _ vm ed => c _ vm _ um ed

theorem reverse_cycle {D V q C} (c : Cycle D V q C) : Cycle (rev D) V q C :=
  ⟨c.sub,c.size,c.incoming,c.heads⟩

/-- A red path out of h and a blue path back to h define a rectangle.
All entries with both boundary paths at most q-1 are missing. -/
theorem interior {D V C N q col h x y m n} (free : QFree D V q) (sw : Switch D V col)
    (cs : C⊆V) (ns : N⊆V) (red : HasColor D C col) (blue : HasColor D N (other col))
    (hc : h∈C) (yn : y∈N) (p : Walk D C h x m) (t : Walk D N y h n)
    (sm : m<q) (sn : n<q) (edge : D x y=true) : False := by
  cases m with
  | zero =>
    cases p
    exact free h _ (by omega) (by omega) (.step (ns yn) edge (t.mono ns))
  | succ m =>
    cases n with
    | zero =>
      cases t
      exact free h _ (by omega) (by omega) ((p.mono cs).snoc (cs hc) edge)
    | succ n =>
      obtain ⟨r,prev,xm,rx⟩ := p.unsnoc
      have rc : r∈C := prev.end_mem_or.elim (fun eq => eq ▸ hc) id
      cases t with
      | step zn yz rest =>
        by_cases c : col x y
        · exact interior free sw cs ns red blue hc zn p rest sm (by omega)
            (sw x (cs xm) y (ns yn) _ (ns zn) edge yz (fun eq => blue _ yn _ zn yz (eq.mp c)))
        · exact interior free sw cs ns red blue hc yn prev (.step zn yz rest) (by omega) sn
            (sw r (cs rc) x (cs xm) y (ns yn) rx edge (fun eq => c (eq.mp (red _ rc _ xm rx))))
termination_by m+n

private theorem back_short {D V N q h s z} (hq : 2≤q) (free : QFree D V q) (cn : Cycle D V q N)
    (hn : h∈N) (sn : s∈N) (zn : z∈N) (hs : D h s=true) (ne : z≠s) :
    ∃n,n<q ∧ Walk D N z h n := by
  by_cases eq : z=h
  · exact ⟨0,by omega,eq ▸ .refl _⟩
  obtain ⟨lo,hi,p,t⟩ := MandatoryExcursion.segments (by omega : 1≤q) free cn hn zn
  let d := MandatoryExcursion.span D V q h z
  change 1≤d at lo
  change Walk D N h z d at p
  have two : 2≤d := by
    by_contra! low
    rw [show d=1 by omega] at p
    cases p with | step _ hz rest =>
      cases rest
      exact ne (card_le_one.mp (cn.heads h hn).le _ (mem_outN.mpr ⟨zn,hz⟩) _ (mem_outN.mpr ⟨sn,hs⟩))
  exact ⟨q+1-d,by omega,t⟩

private theorem along {D V} {P : ℕ→Prop} (step : ∀u∈V,∀v∈V,D u v=true → P u → P v)
    {u v n} (path : Walk D V u v n) (uv : u∈V) (start : P u) : P v := by
  induction path with
  | refl => exact start
  | step bv e _ ih => exact ih bv (step _ uv _ bv e start)

/-- If the corner takes the incoming color, its tail has an arc of that
color to every vertex of the outgoing cycle. -/
theorem fan {D V C N q col h p s} (hq : 2≤q) (free : QFree D V q) (sw : Switch D V col)
    (cc : Cycle D V q C) (cn : Cycle D V q N) (red : HasColor D C col) (blue : HasColor D N (other col))
    (hc : h∈C) (hn : h∈N) (pc : p∈C) (sn : s∈N) (ph : D p h=true) (hs : D h s=true)
    (corner : col p s) : ∀z∈N,D p z=true ∧ col p z := by
  have init := sw p (cc.sub pc) h (cc.sub hc) s (cn.sub sn) ph hs (fun eq => blue _ hn _ sn hs (eq.mp (red _ pc _ hc ph)))
  have hp : Walk D C h p q := by
    simpa using NativeSharedSegment.complement (by omega : 1≤q) free cc pc
      (.step hc ph (.refl _) : Walk D C p h 1) (by omega)
  let k := q-1
  have len : q=k+1 := by dsimp [k]; omega
  obtain ⟨r,prior,_,rp⟩ := (show Walk D C h p (k+1) by rwa [←len]).unsnoc
  have rc := prior.end_mem_or.elim (fun eq => eq ▸ hc) id
  have step (u) (un : u∈N) (v) (vn : v∈N) (uv : D u v=true) (pu : D p u=true ∧ col p u) :
      D p v=true ∧ col p v := by
    have pv := sw p (cc.sub pc) u (cn.sub un) v (cn.sub vn) pu.1 uv (fun eq => blue _ un _ vn uv (eq.mp pu.2))
    refine ⟨pv,?_⟩
    by_cases eq : v=s
    · exact eq ▸ corner
    by_contra otherColor
    have rv := sw r (cc.sub rc) p (cc.sub pc) v (cn.sub vn) rp pv (fun eq => otherColor (eq.mp (red _ rc _ pc rp)))
    obtain ⟨n,lt,ret⟩ := back_short hq free cn hn sn vn hs eq
    exact interior free sw cc.sub cn.sub red blue hc vn prior ret (by omega) lt rv
  intro z zn
  obtain ⟨_,_,path,_⟩ := MandatoryExcursion.segments (by omega : 1≤q) free cn sn zn
  exact along step path sn ⟨init,corner⟩

/-- At a red-to-blue corner one of the two entire monochromatic fans is forced. -/
theorem corner {D V C N q col h p s} (hq : 2≤q) (free : QFree D V q) (sw : Switch D V col)
    (cc : Cycle D V q C) (cn : Cycle D V q N) (red : HasColor D C col) (blue : HasColor D N (other col))
    (hc : h∈C) (hn : h∈N) (pc : p∈C) (sn : s∈N) (ph : D p h=true) (hs : D h s=true) :
    (∀z∈N,D p z=true ∧ col p z) ∨ (∀z∈C,D z s=true ∧ ¬col z s) := by
  classical
  by_cases hit : col p s
  · exact Or.inl (fan hq free sw cc cn red blue hc hn pc sn ph hs hit)
  right
  have twice : HasColor (rev D) C (other (flip (other col))) :=
    fun u uc v vc vu no => no (red v vc u uc vu)
  exact fan hq free.reverse sw.other.rev (reverse_cycle cn) (reverse_cycle cc)
    blue.rev twice hn hc sn pc hs ph hit

#print axioms interior
#print axioms corner
end LeanCH.BR.Closure.SharedArcGrid
