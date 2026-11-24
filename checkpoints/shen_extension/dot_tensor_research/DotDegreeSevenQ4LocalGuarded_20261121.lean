import LeanCH.BR.BRShortestCycle
import LeanCH.BR.BRCycleReturn
namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen
set_option maxHeartbeats 1000000

def LocalFull (D : CH.Digraph) (A : Finset ℕ) (u : ℕ) : Prop :=
  (outN D A u).card = 1

def LocalGuarded (D : CH.Digraph) (A : Finset ℕ) (u : ℕ) : Prop :=
  ∃ f ∈ ball D A u 2, LocalFull D A f

/-- With two full labels, every unguarded row has no incoming arc. -/
theorem local_unguarded_source_q4 {D : CH.Digraph} {A : Finset ℕ} {u f g : ℕ}
    (hf : QFree D A 4) (hc : A.card = 7)
    (hm : ∀ v ∈ A, 1 ≤ (outN D A v).card)
    (hu : u ∈ A) (hfA : f ∈ A) (hgA : g ∈ A) (hfg : f ≠ g)
    (hff : LocalFull D A f) (hgg : LocalFull D A g)
    (hng : ¬ LocalGuarded D A u) :
    ∀ v ∈ A, D v u ≠ true := by
  classical
  have no1 (x : ℕ) (hx : x ∈ A) : D x x ≠ true := fun e =>
    hf x 1 (by decide) (by decide) (.step hx e (.refl x))
  have no2 (x y : ℕ) (hx : x ∈ A) (hy : y ∈ A) (e : D x y = true) :
      D y x ≠ true := fun r =>
    hf x 2 (by decide) (by decide) (.step hy e (.step hx r (.refl x)))
  have no3 (x y z : ℕ) (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
      (e : D x y = true) (r : D y z = true) : D z x ≠ true := fun k =>
    hf x 3 (by decide) (by decide) (.step hy e (.step hz r (.step hx k (.refl x))))
  have no4 (x y z w : ℕ) (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A) (hw : w ∈ A)
      (e : D x y = true) (r : D y z = true) (k : D z w = true) : D w x ≠ true :=
    fun t => hf x 4 (by decide) (by decide)
      (.step hy e (.step hz r (.step hw k (.step hx t (.refl x)))))
  have large (v : ℕ) (hv : v ∈ ball D A u 2) : 1 < (outN D A v).card := by
    have mn := hm v (ball_subset hv)
    have neq : ¬ LocalFull D A v := fun hvf => hng ⟨v,hv,hvf⟩
    unfold LocalFull at neq
    omega
  have step1 (x : ℕ) (hx : x ∈ A) (ex : D u x = true) : x ∈ ball D A u 2 :=
    ball_mono_radius (by decide : 1 ≤ 2) (ball_of_adj hx ex)
  have step2 (x y : ℕ) (hx : x ∈ A) (hy : y ∈ A) (ex : D u x = true)
      (ey : D x y = true) : y ∈ ball D A u 2 :=
    ball_step (ball_of_adj hx ex) hy ey
  have u2 : u ∈ ball D A u 2 := self_mem_ball hu
  have separate (x : ℕ) (hx : x ∈ ball D A u 2) : x ≠ f ∧ x ≠ g := by
    constructor
    · intro e; subst x; exact hng ⟨f,hx,hff⟩
    · intro e; subst x; exact hng ⟨g,hx,hgg⟩
  have ab : ∃ a b, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧
      D u a = true ∧ D u b = true ∧ D b a ≠ true := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (large u u2)
    obtain ⟨ha, ua⟩ := mem_outN.mp ha
    obtain ⟨hb, ub⟩ := mem_outN.mp hb
    by_cases ba : D b a = true
    · exact ⟨b,a,hb,ha,hab.symm,ub,ua,no2 b a hb ha ba⟩
    · exact ⟨a,b,ha,hb,hab,ua,ub,ba⟩
  obtain ⟨a,b,ha,hb,hab,ua,ub,ba⟩ := ab
  obtain ⟨c,hcN,d,hdN,hcd⟩ := Finset.one_lt_card.mp (large b (step1 b hb ub))
  obtain ⟨hcA,bc⟩ := mem_outN.mp hcN
  obtain ⟨hdA,bd⟩ := mem_outN.mp hdN
  have au : a ≠ u := by rintro rfl; exact no1 a ha ua
  have bu : b ≠ u := by rintro rfl; exact no1 b hb ub
  have cu : c ≠ u := by rintro rfl; exact no2 c b hu hb ub bc
  have du : d ≠ u := by rintro rfl; exact no2 d b hu hb ub bd
  have ca : c ≠ a := by rintro rfl; exact ba bc
  have da : d ≠ a := by rintro rfl; exact ba bd
  have cb : c ≠ b := by rintro rfl; exact no1 c hcA bc
  have db : d ≠ b := by rintro rfl; exact no1 d hdA bd
  obtain ⟨uf, ug⟩ := separate u u2
  obtain ⟨af, ag⟩ := separate a (step1 a ha ua)
  obtain ⟨bf, bg⟩ := separate b (step1 b hb ub)
  obtain ⟨cf, cg⟩ := separate c (step2 b c hb hcA ub bc)
  obtain ⟨df, dg⟩ := separate d (step2 b d hb hdA ub bd)
  let all : Finset ℕ := {a,b,c,d,u,f,g}
  have caa : all.card = 7 := by
    simp [all, Finset.card_insert_of_notMem, hab, hcd, hfg, au, bu, cu, du,
      uf, ug, af, ag, bf, bg, cf, cg, df, dg, Ne.symm ca, Ne.symm da, Ne.symm cb, Ne.symm db]
  have sub : all ⊆ A := by
    intro x hx
    simp only [all, mem_insert, mem_singleton] at hx
    rcases hx with e|e|e|e|e|e|e <;> subst x <;> assumption
  have eqA := Finset.eq_of_subset_of_card_le sub (by omega)
  have cases (x : ℕ) (hx : x ∈ A) :
      x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = u ∨ x = f ∨ x = g := by
    rw [← eqA] at hx
    simpa [all] using hx
  have ac_ad : D c a ≠ true ∧ D d a ≠ true := by
    by_cases e : D a b = true
    · exact ⟨no3 a b c ha hb hcA e bc, no3 a b d ha hb hdA e bd⟩
    · have suba : outN D A a ⊆ {c,d} := by
        intro x hx
        obtain ⟨hx, ax⟩ := mem_outN.mp hx
        rcases cases x hx with ee|ee|ee|ee|ee|ee|ee <;> subst x
        · exact (no1 a ha ax).elim
        · exact (e ax).elim
        · simp
        · simp
        · exact (no2 u a hu ha ua ax).elim
        · exact ((separate f (step2 a f ha hfA ua ax)).1 rfl).elim
        · exact ((separate g (step2 a g ha hgA ua ax)).2 rfl).elim
      have le := large a (step1 a ha ua)
      have eq : outN D A a = {c,d} := Finset.eq_of_subset_of_card_le suba (by simp [hcd]; omega)
      have ac := (mem_outN.mp (show c ∈ outN D A a by simp [eq])).2
      have ad := (mem_outN.mp (show d ∈ outN D A a by simp [eq])).2
      exact ⟨no2 a c ha hcA ac,no2 a d ha hdA ad⟩
  have ncf (p z : ℕ) (hp : p ∈ A) (hz : z ∈ A) (bc' : D b p = true)
      (hz' : D z u = true) : D p z ≠ true :=
    fun e => no4 u b p z hu hb hp hz ub bc' e hz'
  have nofull (p t : ℕ) (hp : p ∈ A) (ht : t ∈ A)
      (hpt : ∀ x ∈ A, x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = u ∨ x = p ∨ x = t) :
      D p u ≠ true := by
    intro pu
    have sc : outN D A c ⊆ {d,t} := by
      intro x hx
      obtain ⟨hx,cx⟩ := mem_outN.mp hx
      rcases hpt x hx with ee|ee|ee|ee|ee|ee|ee <;> subst x
      · exact (ac_ad.1 cx).elim
      · exact (no2 b c hb hcA bc cx).elim
      · exact (no1 c hcA cx).elim
      · simp
      · exact (no3 u b c hu hb hcA ub bc cx).elim
      · exact (ncf c p hcA hp bc pu cx).elim
      · simp
    have sd : outN D A d ⊆ {c,t} := by
      intro x hx
      obtain ⟨hx,dx⟩ := mem_outN.mp hx
      rcases hpt x hx with ee|ee|ee|ee|ee|ee|ee <;> subst x
      · exact (ac_ad.2 dx).elim
      · exact (no2 b d hb hdA bd dx).elim
      · simp
      · exact (no1 d hdA dx).elim
      · exact (no3 u b d hu hb hdA ub bd dx).elim
      · exact (ncf d p hdA hp bd pu dx).elim
      · simp
    have lc := large c (step2 b c hb hcA ub bc)
    have ld := large d (step2 b d hb hdA ub bd)
    have ec : outN D A c = {d,t} := Finset.eq_of_subset_of_card_le sc
      (le_trans (Finset.card_insert_le _ _) (by simp; omega))
    have ed : outN D A d = {c,t} := Finset.eq_of_subset_of_card_le sd
      (le_trans (Finset.card_insert_le _ _) (by simp; omega))
    exact no2 c d hcA hdA
      (mem_outN.mp (show d ∈ outN D A c by simp [ec])).2
      (mem_outN.mp (show c ∈ outN D A d by simp [ed])).2
  intro v hv
  rcases cases v hv with ee|ee|ee|ee|ee|ee|ee <;> subst v
  · exact no2 u a hu ha ua
  · exact no2 u b hu hb ub
  · exact no3 u b c hu hb hcA ub bc
  · exact no3 u b d hu hb hdA ub bd
  · exact no1 u hu
  · exact nofull f g hfA hgA cases
  · exact nofull g f hgA hfA (fun x hx => by rcases cases x hx with h|h|h|h|h|h|h <;> first | exact Or.inl h | exact Or.inr (Or.inl h) | exact Or.inr (Or.inr (Or.inl h)) | exact Or.inr (Or.inr (Or.inr (Or.inl h))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

/-- Two degree-one rows exist in any seven-label sinkless 4-free host. -/
theorem local_two_full_q4 {D : CH.Digraph} {A : Finset ℕ}
    (hf : QFree D A 4) (hc : A.card = 7)
    (hm : ∀ v ∈ A, 1 ≤ (outN D A v).card) :
    ∃ f ∈ A, ∃ g ∈ A, f ≠ g ∧ LocalFull D A f ∧ LocalFull D A g := by
  classical
  obtain ⟨p,M,hp,hfree,hMA,hM,cy⟩ :=
    exists_minimal_cycle_support (by decide : 1 ≤ 4) hf hm (Finset.card_pos.mp (by omega))
  let E := A \ M
  have hE : E.card = 7 - M.card := by rw [Finset.card_sdiff_of_subset hMA, hc]
  have eA {z : ℕ} (hz : z ∈ E) : z ∈ A := (mem_sdiff.mp hz).1
  have eM {z : ℕ} (hz : z ∈ E) : z ∉ M := (mem_sdiff.mp hz).2
  have no1 {v : ℕ} (hv : v ∈ A) : D v v ≠ true := fun e =>
    hf v 1 (by decide) (by decide) (.step hv e (.refl v))
  have no2 {v w : ℕ} (hv : v ∈ A) (hw : w ∈ A) (e : D v w = true) :
      D w v ≠ true := fun r =>
    hf v 2 (by decide) (by decide) (.step hw e (.step hv r (.refl v)))
  have no3 {v w z : ℕ} (hv : v ∈ A) (hw : w ∈ A) (hz : z ∈ A)
      (e : D v w = true) (r : D w z = true) : D z v ≠ true := fun k =>
    hf v 3 (by decide) (by decide) (.step hw e (.step hz r (.step hv k (.refl v))))
  have split {v : ℕ} (hv : v ∈ A) : v ∈ M ∨ v ∈ E := by
    by_cases h : v ∈ M
    · exact Or.inl h
    · exact Or.inr (mem_sdiff.mpr ⟨hv,h⟩)
  have infull {v : ℕ} (hv : v ∈ M) (hn : ∀ z ∈ E, D v z ≠ true) : LocalFull D A v := by
    unfold LocalFull
    have eq : outN D A v = outN D M v := by
      ext x
      simp only [mem_outN]
      exact ⟨fun ⟨hx,e⟩ => ⟨(split hx).resolve_right (fun h => hn x h e),e⟩,
        fun ⟨hx,e⟩ => ⟨hMA hx,e⟩⟩
    rw [eq, cy v hv]
  have parent_cap (z : ℕ) (hz : z ∈ E) (hn : (outN D M z).Nonempty) :
      (inN D M z).card ≤ 2 := by
    by_cases hi : (inN D M z).Nonempty
    · have hh := BRsub.cycle_two_sided_contact_cap (by omega : 2 ≤ p) hfree hMA hM cy (eA hz) hi hn
      have := Finset.card_pos.mpr hn
      omega
    · have he : (inN D M z).card = 0 := Nat.eq_zero_of_not_pos (fun h => hi (Finset.card_pos.mp h))
      omega
  have two_from (S : Finset ℕ) (hS : 1 < S.card) (hSM : S ⊆ M)
      (hg : ∀ v ∈ S, LocalFull D A v) :
      ∃ f ∈ A, ∃ g ∈ A, f ≠ g ∧ LocalFull D A f ∧ LocalFull D A g := by
    obtain ⟨v,hv,w,hw,hvw⟩ := Finset.one_lt_card.mp hS
    exact ⟨v,hMA (hSM hv),w,hMA (hSM hw),hvw,hg v hv,hg w hw⟩
  have repair_full (z w : ℕ) (hz : z ∈ E) (hw : w ∈ E) (hzw : z ≠ w)
      (hpair : E = {z,w}) (hn : ¬ (outN D M z).Nonempty) :
      ∃ f ∈ A, ∃ g ∈ A, f ≠ g ∧ LocalFull D A f ∧ LocalFull D A g := by
    have subz : outN D A z ⊆ {w} := by
      intro x hx
      obtain ⟨hx,zx⟩ := mem_outN.mp hx
      rcases split hx with xM|xE
      · exact (hn ⟨x,mem_outN.mpr ⟨xM,zx⟩⟩).elim
      · rw [hpair] at xE
        rcases (show x = z ∨ x = w by simpa using xE) with e|e
        · subst x
          exact (no1 (eA hz) zx).elim
        · simp [e]
    have ez : outN D A z = {w} := Finset.eq_of_subset_of_card_le subz (by simpa using hm z (eA hz))
    have zw := (mem_outN.mp (show w ∈ outN D A z by simp [ez])).2
    have subw : outN D A w ⊆ M := by
      intro x hx
      obtain ⟨hx,wx⟩ := mem_outN.mp hx
      rcases split hx with xM|xE
      · exact xM
      · rw [hpair] at xE
        rcases (show x = z ∨ x = w by simpa using xE) with e|e
        · subst x; exact (no2 (eA hz) (eA hw) zw wx).elim
        · subst x; exact (no1 (eA hw) wx).elim
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (hm w (eA hw))
    have vM := subw hv
    have wv := (mem_outN.mp hv).2
    have vf : LocalFull D A v := infull vM (by
      intro x hx
      rw [hpair] at hx
      rcases (show x = z ∨ x = w by simpa using hx) with e|e
      · subst x
        exact no3 (eA hz) (eA hw) (hMA vM) zw wv
      · subst x
        exact no2 (eA hw) (hMA vM) wv)
    exact ⟨z,eA hz,v,hMA vM,(fun e => eM hz (e.symm ▸ vM)),by simp [LocalFull,ez],vf⟩
  by_cases hE2 : E.card = 2
  · obtain ⟨z,w,hzw,hpair⟩ := Finset.card_eq_two.mp hE2
    have hz : z ∈ E := by simp [hpair]
    have hw : w ∈ E := by simp [hpair]
    by_cases rnz : (outN D M z).Nonempty
    · by_cases rnw : (outN D M w).Nonempty
      · let P := inN D M z ∪ inN D M w
        let S := M \ P
        have subP : P ⊆ M := by
          intro v hv
          rcases mem_union.mp hv with h|h <;> exact (mem_inN.mp h).1
        have hSz : S.card = M.card - P.card := Finset.card_sdiff_of_subset subP
        have capz := parent_cap z hz rnz
        have capw := parent_cap w hw rnw
        have capP : P.card ≤ (inN D M z).card + (inN D M w).card := Finset.card_union_le _ _
        have fullS (v : ℕ) (hv : v ∈ S) : LocalFull D A v := by
          obtain ⟨vM,vP⟩ := mem_sdiff.mp hv
          apply infull vM
          intro x hx vx
          rw [hpair] at hx
          rcases (show x = z ∨ x = w by simpa using hx) with e|e
          · subst x; exact vP (mem_union_left _ (mem_inN.mpr ⟨vM,vx⟩))
          · subst x; exact vP (mem_union_right _ (mem_inN.mpr ⟨vM,vx⟩))
        by_cases two : 1 < S.card
        · exact two_from S two Finset.sdiff_subset fullS
        · have z2 : (inN D M z).card = 2 := by omega
          have w2 : (inN D M w).card = 2 := by omega
          have single (x : ℕ) (hx : x ∈ E) (hret : (outN D M x).Nonempty)
              (hi : (inN D M x).card = 2) : (outN D M x).card = 1 := by
            have cap := BRsub.cycle_two_sided_contact_cap (by omega : 2 ≤ p) hfree hMA hM cy
              (eA hx) (Finset.card_pos.mp (by omega)) hret
            have := Finset.card_pos.mpr hret
            omega
          have extfull (x y : ℕ) (xx : x ∈ E) (yy : y ∈ E) (he : E = {x,y})
              (hno : D x y ≠ true) (hs : (outN D M x).card = 1) : LocalFull D A x := by
            have eq : outN D A x = outN D M x := by
              ext v
              simp only [mem_outN]
              constructor
              · rintro ⟨hv,xv⟩
                rcases split hv with vM|vE
                · exact ⟨vM,xv⟩
                · rw [he] at vE
                  rcases (show v = x ∨ v = y by simpa using vE) with e|e
                  · subst v; exact (no1 (eA xx) xv).elim
                  · subst v; exact (hno xv).elim
              · rintro ⟨hv,xv⟩
                exact ⟨hMA hv,xv⟩
            simpa only [LocalFull, eq] using hs
          obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
          have vM := Finset.sdiff_subset hv
          by_cases zw : D z w = true
          · have fw := extfull w z hw hz (hpair.trans (by ext x; simp [or_comm]))
              (no2 (eA hz) (eA hw) zw) (single w hw rnw w2)
            exact ⟨v,hMA vM,w,eA hw,fun e => eM hw (e ▸ vM),fullS v hv,fw⟩
          · have fz := extfull z w hz hw hpair zw (single z hz rnz z2)
            exact ⟨v,hMA vM,z,eA hz,fun e => eM hz (e ▸ vM),fullS v hv,fz⟩
      · exact repair_full w z hw hz hzw.symm
          (hpair.trans (by ext x; simp [or_comm])) rnw
    · exact repair_full z w hz hw hzw hpair rnz
  · by_cases nz : E.Nonempty
    · obtain ⟨z,hz⟩ := nz
      have ec : E.card ≤ 1 := by omega
      have only {x : ℕ} (hx : x ∈ E) : x = z := Finset.card_le_one.mp ec x hx z hz
      have rn : (outN D M z).Nonempty := by
        obtain ⟨x,hx⟩ := Finset.card_pos.mp (hm z (eA hz))
        obtain ⟨hx,zx⟩ := mem_outN.mp hx
        rcases split hx with xM|xE
        · exact ⟨x,mem_outN.mpr ⟨xM,zx⟩⟩
        · have ex := only xE
          subst x
          exact (no1 (eA hz) zx).elim
      let S := M \ inN D M z
      have cap := parent_cap z hz rn
      have hS : S.card = M.card - (inN D M z).card :=
        Finset.card_sdiff_of_subset (fun _ h => (mem_inN.mp h).1)
      refine two_from S (by omega) Finset.sdiff_subset ?_
      intro v hv
      obtain ⟨vM,vP⟩ := mem_sdiff.mp hv
      apply infull vM
      intro x hx vx
      have ex := only hx
      subst x
      exact vP (mem_inN.mpr ⟨vM,vx⟩)
    · exact two_from M (by omega) (fun _ h => h) (fun v hv =>
        infull hv (fun x hx => (nz ⟨x,hx⟩).elim))

theorem local_guarded_pair_q4 {D : CH.Digraph} {A : Finset ℕ}
    (hf : QFree D A 4) (hc : A.card = 7)
    (hm : ∀ v ∈ A, 1 ≤ (outN D A v).card) :
    ∃ P ⊆ A, P.card = 2 ∧ ∀ c ∈ P, (outN D A c).card = 1 ∧
      ∃ s ∈ A, ∃ a ∈ A, D c s = true ∧ D s a = true ∧
        LocalGuarded D A s ∧ LocalGuarded D A a := by
  classical
  obtain ⟨f,hfA,g,hgA,fg,ff,gg⟩ := local_two_full_q4 hf hc hm
  have guarded (u v : ℕ) (hu : u ∈ A) (hv : v ∈ A) (e : D u v = true) :
      LocalGuarded D A v := by
    by_contra h
    exact local_unguarded_source_q4 hf hc hm hv hfA hgA fg ff gg h u hu e
  refine ⟨{f,g}, ?_, by simp [fg], ?_⟩
  · intro v hv
    rcases (show v = f ∨ v = g by simpa using hv) with e|e <;> subst v <;> assumption
  · intro c h
    have hcf : c ∈ A ∧ LocalFull D A c := by
      rcases (show c = f ∨ c = g by simpa using h) with e|e <;> subst c
      · exact ⟨hfA,ff⟩
      · exact ⟨hgA,gg⟩
    obtain ⟨s,hs⟩ := Finset.card_pos.mp (hm c hcf.1)
    obtain ⟨hs,cs⟩ := mem_outN.mp hs
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (hm s hs)
    obtain ⟨ha,sa⟩ := mem_outN.mp ha
    exact ⟨hcf.2,s,hs,a,ha,cs,sa,guarded c s hcf.1 hs cs,guarded s a hs ha sa⟩

#print axioms local_guarded_pair_q4
end LeanCH.BR.DotDegreeSevenLow


