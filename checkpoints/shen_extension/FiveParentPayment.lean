import checkpoints.shen_extension.FiveParentDeletion

namespace LeanCH.BR.ShenPuncture.FiveParent
open BRq2 BRq3 Finset WeightedSD

private theorem tri {D W a b c} (free : QFree D W 3) (ha : a∈W) (hb : b∈W) (hc : c∈W)
    (ab : D a b=true) (bc : D b c=true) : D c a≠true := fun ca =>
  free a 3 (by decide) le_rfl (.step hb ab (.step hc bc (.step ha ca (.refl a))))

private theorem safe_two {D W t z} (ne : z≠t) (no : D z t≠true)
    (cut : ∀ m∈W, D z m=true → D m t≠true) : t∉ball D W z 2 := by
  intro h
  obtain ⟨_,j,hj,p⟩ := mem_ball.mp h
  interval_cases j
  · cases p; exact ne rfl
  · cases p with | step _ e p => cases p; exact no e
  · cases p with | step hm e p => cases p with | step _ f p => cases p; exact cut _ hm e f

/-- Delete y, fill a with b, and replace b's lost head q by the full row f.
All other lost old edges in a row point to either a or b. A parent of b
cannot also be its head. Any row fed by b or f avoids the deleted y. -/
theorem paid_chain {D : CH.Digraph} {W : Finset ℕ} {d a b q f y : ℕ}
    (free : QFree D W 3) (size : W.card≤3*d+1) (law : BankLaw d)
    (degree : ∀ x∈W, d≤(outN D W x).card)
    (ha : a∈W) (hb : b∈W) (hq : q∈W) (hf : f∈W) (hy : y∈W)
    (ay : D a y=true) (yb : D y b=true) (yf : D y f=true) (af : D a f=true)
    (bq : D b q=true) (richF : d<(outN D W f).card)
    (missing : D a b≠true) (bf : b≠f)
    (parentY : ∀ x∈W, (outN D W x).card=d → D x y=true → x=a)
    (parentA : ∀ x∈W, (outN D W x).card=d → D x a=true → x=q)
    (noTight : ∀ x∈W, (outN D W x).card=d → D f x=true → D x b≠true) :
    D b f=true := by
  classical
  by_contra fresh
  let V := W.erase y
  let C : CH.Digraph := fun x v => if (x=b ∧ v=q) ∨
    (x≠q ∧ D b x=true ∧ v=a) ∨ ((x=f ∨ D f x=true) ∧ v=b) then false else D x v
  let L := insertArc C a b
  let G := insertArc L b f
  have sub {x v} (e : C x v=true) : D x v=true := by dsimp [C] at e; split at e <;> simp_all
  have kept {x v} (e : D x v=true) (i : ¬(x=b ∧ v=q))
      (j : ¬(x≠q ∧ D b x=true ∧ v=a)) (k : ¬((x=f ∨ D f x=true) ∧ v=b)) : C x v=true := by
    dsimp [C]; split
    · tauto
    · exact e
  have ba := tri free ha hy hb ay yb
  have fa := digonfree free (by decide) ha hf af
  have ayN : a≠y := fun e => loopfree free (by decide) hy (e ▸ ay)
  have byN : b≠y := fun e => loopfree free (by decide) hy (e ▸ yb)
  have fyN : f≠y := fun e => loopfree free (by decide) hy (e ▸ yf)
  have ab : a≠b := fun e => digonfree free (by decide) ha hy ay (e ▸ yb)
  have afN : a≠f := fun e => loopfree free (by decide) hf (e ▸ af)
  have av : a∈V := mem_erase.mpr ⟨ayN,ha⟩
  have bv : b∈V := mem_erase.mpr ⟨byN,hb⟩
  have fv : f∈V := mem_erase.mpr ⟨fyN,hf⟩
  have cf : QFree C V 3 := (qfree_sub (fun _ _ => sub) free).mono_set (erase_subset _ _)
  have safe1 : a∉ball C V b 2 := by
    apply safe_two ab.symm (fun e => ba (sub e))
    intro m _ bm ma
    by_cases mq : m=q
    · simp [C,mq] at bm
    · have bm' := sub bm; simp [C,mq,bm'] at ma
  have lf : QFree L V 3 := qfree_insertArc cf ⟨a,av⟩ ⟨b,bv⟩ safe1
  have fromF (v) : L f v=C f v := by simp [L,insertArc,afN.symm]
  have safe2 : b∉ball L V f 2 := by
    apply safe_two bf.symm (by simp [fromF,C])
    intro m _ fm mb
    rw [fromF] at fm
    by_cases ma : m=a
    · exact fa (ma ▸ sub fm)
    · have fm' := sub fm
      simp [L,insertArc,ma,C,fm'] at mb
  have gf : QFree G V 3 := qfree_insertArc lf ⟨b,bv⟩ ⟨f,fv⟩ safe2
  have vc : V.card=W.card-1 := card_erase_of_mem hy
  apply (bankLaw_iff _).mp law G V gf ⟨a,av⟩ (by omega)
  intro x xv
  have xW := mem_of_mem_erase xv
  let O := outN D W x
  let N := outN G V x
  change d≤N.card
  have deg : d≤O.card := degree x xW
  have keep {v} (hit : v∈O) (vy : v≠y) (i : ¬(x=b ∧ v=q))
      (j : ¬(x≠q ∧ D b x=true ∧ v=a)) (k : ¬((x=f ∨ D f x=true) ∧ v=b)) : v∈N :=
    mem_outN.mpr ⟨mem_erase.mpr ⟨vy,outN_subset hit⟩,
      insertArc_mono L b f x v (insertArc_mono C a b x v (kept (mem_outN.mp hit).2 i j k))⟩
  have swap {old new} (hit : old∈O) (newN : new∈N) (miss : new∉O) (incl : O.erase old⊆N) : d≤N.card := by
    have le := card_le_card (insert_subset newN incl)
    rw [card_insert_of_notMem (fun h => miss (mem_of_mem_erase h)),card_erase_of_mem hit] at le
    have := card_pos.mpr ⟨old,hit⟩; omega
  have spare {v} (rich : d<O.card) (incl : O.erase v⊆N) : d≤N.card := by
    have le := card_le_card incl
    by_cases j : v∈O
    · rw [card_erase_of_mem j] at le; omega
    · rw [erase_eq_of_notMem j] at le; omega
  by_cases xa : x=a
  · subst x
    apply swap (old:=y) (new:=b) (mem_outN.mpr ⟨hy,ay⟩)
      (mem_outN.mpr ⟨bv,insertArc_mono L b f a b (by simp [L,insertArc])⟩)
      (fun h => missing (mem_outN.mp h).2)
    intro v h
    exact keep (mem_of_mem_erase h) (mem_erase.mp h).1 (fun e => ab e.1)
      (fun e => ba e.2.1) (fun e => e.1.elim afN fa)
  by_cases xb : x=b
  · subst x
    apply swap (old:=q) (new:=f) (mem_outN.mpr ⟨hq,bq⟩) (mem_outN.mpr ⟨fv,by simp [G,insertArc]⟩)
      (fun h => fresh (mem_outN.mp h).2)
    intro v h
    have e := (mem_outN.mp (mem_of_mem_erase h)).2
    exact keep (mem_of_mem_erase h)
      (fun eq => digonfree free (by decide) hy hb yb (eq ▸ e))
      (fun eq => (mem_erase.mp h).1 eq.2) (fun eq => loopfree free (by decide) hb eq.2.1)
      (fun eq => loopfree free (by decide) hb (eq.2 ▸ e))
  by_cases small : O.card=d
  · apply deg.trans (card_le_card (show O⊆N from ?_))
    intro v h
    have e := (mem_outN.mp h).2
    apply keep h (fun eq => xa (parentY x xW small (eq ▸ e))) (fun eq => xb eq.1)
      (fun eq => eq.1 (parentA x xW small (eq.2.2 ▸ e)))
    rintro ⟨xf,vb⟩
    rcases xf with xf|fx
    · change (outN D W x).card=d at small
      rw [xf] at small; omega
    · exact noTight x xW small fx (vb ▸ e)
  have rich : d<O.card := by omega
  by_cases xy : D x y=true
  · apply spare (v:=y) rich
    intro v h
    refine keep (mem_of_mem_erase h) (mem_erase.mp h).1 (fun eq => xb eq.1)
      (fun eq => tri free hy hb xW yb eq.2.1 xy) (fun eq => ?_)
    rcases eq.1 with xf|fx
    · exact digonfree free (by decide) hy hf yf (xf ▸ xy)
    · exact tri free hy hf xW yf fx xy
  have vy {v} (h : v∈O) : v≠y := fun eq => xy (eq ▸ (mem_outN.mp h).2)
  by_cases bx : D b x=true
  · apply spare (v:=a) rich
    intro v h
    have m := mem_of_mem_erase h
    exact keep m (vy m) (fun eq => xb eq.1) (fun eq => (mem_erase.mp h).1 eq.2.2)
      (fun eq => digonfree free (by decide) hb xW bx (eq.2 ▸ (mem_outN.mp m).2))
  · apply spare (v:=b) rich
    intro v h
    have m := mem_of_mem_erase h
    exact keep m (vy m) (fun eq => xb eq.1) (fun eq => bx eq.2.1)
      (fun eq => (mem_erase.mp h).1 eq.2)

#print axioms paid_chain

/-- If a full common head is missed by one of the blockers, a paid chain
exists. If f already points to a blocker, choose a source among the one or
two blockers it reaches, so no tight middle can return to the chosen one. -/
theorem both_feed {D : CH.Digraph} {W : Finset ℕ} {d a u v q f y : ℕ}
    (free : QFree D W 3) (size : W.card≤3*d+1) (law : BankLaw d)
    (degree : ∀ x∈W, d≤(outN D W x).card)
    (ha : a∈W) (hu : u∈W) (hv : v∈W) (hq : q∈W) (hf : f∈W) (hy : y∈W)
    (ay : D a y=true) (yu : D y u=true) (yv : D y v=true)
    (yf : D y f=true) (af : D a f=true) (uq : D u q=true) (vq : D v q=true)
    (rich : d<(outN D W f).card) (du : (outN D W u).card=d) (dv : (outN D W v).card=d)
    (au : D a u≠true) (av : D a v≠true)
    (parentY : ∀ x∈W, (outN D W x).card=d → D x y=true → x=a)
    (parentA : ∀ x∈W, (outN D W x).card=d → D x a=true → x=q)
    (only : ∀ x∈W, (outN D W x).card=d → D f x=true → x=u ∨ x=v) :
    D u f=true ∧ D v f=true := by
  have uf : u≠f := fun e => by subst f; omega
  have vf : v≠f := fun e => by subst f; omega
  have forceU (safe : D f v=true → D v u≠true) : D u f=true := by
    apply paid_chain free size law degree ha hu hq hf hy ay yu yf af uq rich au uf parentY parentA
    intro x hx eq fx
    rcases only x hx eq fx with rfl|rfl
    · exact loopfree free (by decide) hu
    · exact safe fx
  have forceV (safe : D f u=true → D u v≠true) : D v f=true := by
    apply paid_chain free size law degree ha hv hq hf hy ay yv yf af vq rich av vf parentY parentA
    intro x hx eq fx
    rcases only x hx eq fx with rfl|rfl
    · exact safe fx
    · exact loopfree free (by decide) hv
  by_cases vu : D v u=true
  · have yesV := forceV (fun _ => digonfree free (by decide) hv hu vu)
    exact ⟨forceU (fun fv => (digonfree free (by decide) hv hf yesV fv).elim),yesV⟩
  · have yesU := forceU (fun _ => vu)
    exact ⟨yesU,forceV (fun fu => (digonfree free (by decide) hu hf yesU fu).elim)⟩

#print axioms both_feed
end LeanCH.BR.ShenPuncture.FiveParent
