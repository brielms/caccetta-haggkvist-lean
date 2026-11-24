import LeanCH.BR.BRAdjacentRelayBanks

namespace LeanCH.BR.WeightedSD.AdjacentRelay
open Finset BRq2 BRq3 BR45 BRsub RelayFold

noncomputable def child (D : CH.Digraph) (V : Finset ℕ) (u h t : ℕ)
    (K : Finset (ℕ×ℕ)) (Q : ℕ→Finset ℕ) : CH.Digraph :=
  RelayFold.graph (precut D u h t) V u h t K Q

namespace Base
variable {D : CH.Digraph} {V : Finset ℕ} {u h t : ℕ} (B : Base D V u h t)
include B
variable {K : Finset (ℕ×ℕ)} {Q : ℕ→Finset ℕ}

/-- On the actual surviving labels this is the original-bank physical surgery.
The old u->t edge is restored by the precut fold, not purchased twice. -/
theorem child_original {a b : ℕ} (hbh : b≠h) :
    child D V u h t K Q a b=RelayFold.graph D V u h t K Q a b := by
  apply Bool.eq_iff_iff.mpr
  by_cases hau : a=u
  · subst a
    by_cases hbt : b=t
    · subst b
      simp only [child,graph_edge,New,B.X0_eq,B.X1_eq,B.R_eq]
      tauto
    · simp only [child,graph_edge,Old,New,B.X0_eq,B.X1_eq,B.R_eq,B.C_eq,
        precut_head hbh hbt]
  · simp only [child,graph_edge,Old,New,B.X0_eq,B.X1_eq,B.R_eq,B.C_eq,precut_row hau]

theorem child_qfree (hQ : Selected D V u h t K Q) : QFree (child D V u h t K Q) (V.erase h) 3 :=
  B.toRelay.graph_qfree ((B.selected_iff K Q).mpr hQ)

omit B in
theorem source_row_other (q : ℕ) {x : ℕ} (hx : x≠u) :
    row q (precut D u h t) V (fun _=>1) x=row q D V (fun _=>1) x := by
  simp only [row,outW,precut_row hx]

/-- Exact original receiver loss, with optional u->h. No degree premise is
imposed on the precut graph. The coefficient is arbitrary. -/
theorem source_row_u (q : ℕ) :
    row q (precut D u h t) V (fun _=>1) u+(q:ℚ)*(1+epsilon D u h)=
      row q D V (fun _=>1) u := by
  have et : eraseArc D u h u t=true := by simp [eraseArc,B.ht.symm,B.adjacent]
  have ht := outW_eraseArc B.tmem et (fun _=>1) u
  simp only [ite_true] at ht
  by_cases eh : D u h=true
  · have hh := outW_eraseArc B.hmem eh (fun _=>1) u
    simp only [ite_true] at hh
    simp only [row,precut,epsilon,eh,ite_true,Nat.cast_one]
    nlinarith only [ht,hh]
  · have he : eraseArc D u h=D := by
      funext x y
      by_cases hx : x=u <;> by_cases hy : y=h <;> simp_all [eraseArc]
    rw [he] at ht
    have heps : epsilon D u h=0 := by simp [epsilon,eh]
    simp only [row,precut,he,heps,Nat.cast_zero]
    nlinarith only [ht]

theorem losses_eq {r : ℕ} (hr : r∈R D V u h t) :
    losses (precut D u h t) V u h t r=outN D V r∩X1 D V u h t := by
  ext z
  have f:=B.R_facts hr
  by_cases hz : z=u
  · subst z
    simp [losses,mem_outN,precut_row f.2.1,B.R_no_receiver hr]
  · simp only [losses,mem_inter,mem_outN,precut_row f.2.1,B.X1_eq,mem_insert,hz,false_or]

theorem row_X0 (hK : ValidCuts D V u h t K) (q : ℕ) {x : ℕ} (hx : x∈X0 D V u h t) :
    row q (child D V u h t K Q) (V.erase h) (boost t) x=row q D V (fun _=>1) x := by
  have hh:=B.toRelay.row_X0 ((B.validCuts_iff K).mpr hK) (Q:=Q) q (B.X0_eq.symm ▸ hx)
  simpa only [child,source_row_other q (B.X_ne (RelayFold.Base.X0_X hx)).1] using hh

theorem row_X1 (hK : ValidCuts D V u h t K) (q : ℕ) {x : ℕ} (hx : x∈X1 D V u h t) :
    row q (child D V u h t K Q) (V.erase h) (boost t) x+q*((cutHeads V K x).card:ℚ)=
      row q D V (fun _=>1) x+q := by
  have hh:=B.toRelay.row_X1 ((B.validCuts_iff K).mpr hK) (Q:=Q) q (B.X1_eq.symm ▸ hx)
  simpa only [child,source_row_other q (B.X_ne (RelayFold.Base.X1_X hx)).1] using hh

theorem row_u (hK : ValidCuts D V u h t K) (q : ℕ) :
    row q (child D V u h t K Q) (V.erase h) (boost t) u+
      q*((C D V u h t).card:ℚ)+q*(epsilon D u h:ℚ)=row q D V (fun _=>1) u+q := by
  have hh:=B.toRelay.row_u ((B.validCuts_iff K).mpr hK) (Q:=Q) q
  have hl:=B.source_row_u q
  rw [B.C_eq] at hh
  change row q (child D V u h t K Q) (V.erase h) (boost t) u+_= _ at hh
  nlinarith only [hh,hl]

theorem row_R (hK : ValidCuts D V u h t K) (hQ : Selected D V u h t K Q)
    (q : ℕ) {x : ℕ} (hx : x∈R D V u h t) :
    row q (child D V u h t K Q) (V.erase h) (boost t) x+
      q*((outN D V x∩X1 D V u h t).card:ℚ)=row q D V (fun _=>1) x+q*((Q x).card:ℚ) := by
  have hh:=B.toRelay.row_R ((B.validCuts_iff K).mpr hK) ((B.selected_iff K Q).mpr hQ)
    q (B.R_eq.symm ▸ hx)
  simpa only [child,B.losses_eq hx,source_row_other q (B.R_facts hx).2.1] using hh

theorem row_other (hK : ValidCuts D V u h t K) (q : ℕ) {x : ℕ}
    (hxu : x≠u) (hx0 : x∉X0 D V u h t) (hx1 : x∉X1 D V u h t) (hxR : x∉R D V u h t) :
    row q (child D V u h t K Q) (V.erase h) (boost t) x+
      q*(if D x h=true then 1 else 0)=row q D V (fun _=>1) x+
        (if x=t then 1 else 0)+q*(if D x t=true then 1 else 0) := by
  have hh:=B.toRelay.row_other ((B.validCuts_iff K).mpr hK) (Q:=Q) q hxu
    (B.X0_eq.symm ▸ hx0) (B.X1_eq.symm ▸ hx1) (B.R_eq.symm ▸ hxR)
  simpa only [child,source_row_other q hxu,precut_row hxu] using hh

end Base
end LeanCH.BR.WeightedSD.AdjacentRelay
