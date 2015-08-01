Require Import Coq.Unicode.Utf8.

Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.choice.
Require Import Ssreflect.seq.

Require Import MathComp.ssrnum MathComp.ssrint MathComp.ssralg MathComp.bigop.

Require Import CoqUtils.ord CoqUtils.fset CoqUtils.partmap CoqUtils.fperm.
Require Import CoqUtils.nominal CoqUtils.string.

Require Import basic structured.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Logic.

Local Open Scope fset_scope.
Local Open Scope state_scope.

Inductive effect :=
| No
| Loop
| Err
| LoopErr.

Definition effect_eq e e' :=
  match e, e' with
  | No, No | Loop, Loop | Err, Err | LoopErr, LoopErr => true
  | _, _ => false
  end.

Lemma effect_eqP : Equality.axiom effect_eq.
Proof. by case=> [] [] /=; constructor. Qed.

Definition effect_eqMixin := EqMixin effect_eqP.
Canonical effect_eqType := Eval hnf in EqType effect effect_eqMixin.

Definition effect_leq e e' :=
  match e, e' with
  | No, _
  | Loop, Loop
  | Err, Err
  | _, LoopErr => true
  | _, _ => false
  end.

Notation "x ⊑ y" := (effect_leq x y) (at level 70, no associativity).

Definition triple e s c s' :=
  match e with
  | No =>
    exists n, eval_com bound_sem s c n = Done s'

  | Loop =>
    forall n, eval_com bound_sem s c n != NotYet ->
              eval_com bound_sem s c n = Done s'

  | Err =>
    exists2 n, eval_com bound_sem s c n != NotYet &
               eval_com bound_sem s c n != Error ->
               eval_com bound_sem s c n = Done s'

  | LoopErr =>
    forall n s'', eval_com bound_sem s c n = Done s'' ->
                  s'' = s'
  end.

Lemma triple_sub e e' s c s' :
  e ⊑ e' ->
  triple e s c s' ->
  triple e' s c s'.
Proof.
case: e e'=> [] [] //= _.
- case=> [n en] n'.
  move: (eval_com_leq bound_sem s c (leq_maxr n n')).
  move: (eval_com_leq bound_sem s c (leq_maxl n n')).
  rewrite en /refine_result
    => /orP [/eqP en' | /eqP en'] /orP [/eqP ->|/eqP en''] //.
  by rewrite en'.
- case=> [n en]; exists n; by [rewrite en|].
- case=> [n en] n' s''.
  move: (eval_com_leq bound_sem s c (leq_maxr n n')).
  move: (eval_com_leq bound_sem s c (leq_maxl n n')).
  rewrite en /refine_result
    => /orP [/eqP en' | /eqP en'] /orP [/eqP ->|/eqP en''] //.
  by rewrite en'' -en' => - [<-].
- move=> P n s'' Pn.
  by move: (P n); rewrite Pn=> /(_ erefl) [<-].
case=> [n n_term Pn] n' s'' en.
move: (eval_com_leq bound_sem s c (leq_maxr n n')) n_term Pn.
move: (eval_com_leq bound_sem s c (leq_maxl n n')).
rewrite en /refine_result
  => /orP [/eqP en' | /eqP en'] /orP [/eqP en''|/eqP en''] //.
  by rewrite en' => _ /(_ erefl).
by rewrite en' -en'' => _ /(_ erefl) [<-].
Qed.

Lemma triple_skip e s : triple e s Skip s.
Proof.
apply: (triple_sub (erefl : No ⊑ e)).
by exists 1=> /=.
Qed.

Lemma triple_seq e s c1 s' c2 s'' :
  triple e s c1 s' ->
  triple e s' c2 s'' ->
  triple e s (Seq c1 c2) s''.
Proof.
case: e=> /=.
- move=> [n1 e1] [n2 e2].
  exists (maxn n1 n2).+1=> /=.
  move: (eval_com_leq bound_sem s c1 (leq_maxl n1 n2)).
  rewrite e1 /refine_result /= => /eqP <-.
  move: (eval_com_leq bound_sem s' c2 (leq_maxr n1 n2)).
  by rewrite e2 /refine_result /= => /eqP <-.
- move=> P1 P2 [|n] //=; move/(_ n): P1.
  case e1: eval_com=> [s'''| |] //= /(_ erefl) //.
  by move=> [->] {e1 s'''}; eauto.
- case=> [n1 n1_term Pn1] [n2 n2_term Pn2].
  move: (eval_com_leq bound_sem s' c2 (leq_maxr n1 n2)) n2_term Pn2.
  move: (eval_com_leq bound_sem s c1 (leq_maxl n1 n2)) n1_term Pn1.
  rewrite /refine_result; case: eval_com=> [s'''| |] //= /eqP/esym e1 _.
    move=> /(_ erefl) [e].
    rewrite {}e {s'''} in e1 *.
    case: eval_com=> [s'''| |] //= /eqP/esym //= e2 _.
      move=> /(_ erefl) [e].
      rewrite {}e in e2 *.
      by exists (maxn n1 n2).+1; rewrite /= e1 e2.
    by move=> _; exists (maxn n1 n2).+1; rewrite /= e1 e2.
  by exists (maxn n1 n2).+1; rewrite /= e1.
move=> P1 P2 [|n] s''' //=.
case e1: eval_com=> [s''''| |] //=.
by move/(_ _ _ e1): P1=> -> {e1 s''''}; eauto.
Qed.

Definition lh i (vs : seq value) :=
  if vs is [::] then VNil else VPtr (i, 0)%R.

Fixpoint lb i vs :=
  if vs is v :: vs' then
    new (i |: names vs)
        (fun i' => i :-> [:: v; lh i' vs] * lb i' vs')
  else emp.

Lemma rename_lh pm i vs :
  rename pm (lh i vs) = lh (pm i) (rename pm vs).
Proof. by case: vs. Qed.

Lemma names_lh i vs : names (lh i vs) = if nilp vs then fset0 else fset1 i.
Proof. by case: vs=> //= _ _; rewrite namesvE. Qed.


Lemma vars_lb i vs : vars_s (lb i vs) = fset0.
Proof.
elim: vs i => /= [|v vs IH] /= i; first by rewrite vars_emp.
by rewrite /new -lock vars_s_hide vars_s_stateu vars_s_blockat IH fsetU0.
Qed.

Lemma pub_lb i vs : pub (lb i vs) = if vs is [::] then fset0 else fset1 i.
Proof.
elim: vs i=> //= [|v vs IH] i; first by rewrite pub_emp.
rewrite /new -lock pub_hide.
move: (fresh _) (freshP (i |: names (v :: vs)))=> i'.
rewrite in_fsetU1 namess1 in_fsetU !negb_or => /and3P [ii' iv ivs].
rewrite pubU IH pub_blockat.
case: vs {IH ivs} => [|v' vs'] //=.
  rewrite fsetU0; apply/eq_fset=> i''.
  rewrite in_fsetD1 in_fset1.
  have [->|] //= := altP (i'' =P i').
  by rewrite (negbTE ii').
apply/eq_fset=> i''; rewrite in_fsetD1 in_fsetU !in_fset1.
have [->|] //= := altP (i'' =P i').
  by rewrite (negbTE ii').
by rewrite orbF.
Qed.

Lemma names_lb i vs :
  names (lb i vs) = pub (lb i vs) :|: names vs.
Proof.
elim: vs i => [|v vs IH] i /=.
  by rewrite names_emp pub_emp fset0U namess0.
rewrite /new -lock.
move: (fresh _) (freshP (i |: names (v :: vs)))=> i'.
rewrite namess1 => nin.
move: (nin); rewrite in_fsetU1 in_fsetU !negb_or=> /and3P [ii' ninv ninvs].
rewrite names_hide names_stateu; first last.
  rewrite pub_blockat pub_lb; case: (vs)=> // _ _.
    by apply/fdisjointP=> i'' /fset1P ->; rewrite in_fset1 eq_sym.
  by rewrite !vars_s_blockat fdisjoint0.
rewrite pub_hide pubU pub_blockat names_blockat /= namessE /=.
rewrite fsetU0 !fsetUA /= namesT fsetU0 fsetU1E namesnE {}IH.
rewrite !fsetD1U -!fsetUA; congr fsetU.
rewrite fsetUA fsetUC -!fsetUA; congr fsetU.
rewrite [fset1 _ :\ _]fsetD1E fsetDv fsetU0 fsetUC; congr fsetU.
  apply/eqP; rewrite eqEfsubset fsubD1set fsetU1E fsubsetUr /=.
  apply/fsubsetP=> i'' inv; rewrite in_fsetD1 inv andbT.
  by apply: contra ninv=> /eqP <-.
apply/eqP; rewrite eqEfsubset fsubD1set fsetU1E fsubsetUr /=.
apply/fsubsetP=> i'' inv; rewrite in_fsetD1 inv andbT.
by apply: contra ninvs=> /eqP <-.
Qed.

Lemma rename_lb pm i vs :
  rename pm (lb i vs) = lb (pm i) (rename pm vs).
Proof.
elim: vs pm i=> [|v vs IH] pm i /=.
  by apply/names0P; rewrite names_emp.
rewrite rename_new; last first.
  move=> {pm} pm dis /= i'.
  rewrite rename_stateu rename_blockat /= renamenE IH.
  move: dis; rewrite fsetU1E namess1 2!fdisjointUr fdisjoints1.
  case/and3P=> [/suppPn pm_i disv disvs].
  rewrite pm_i renamesE /= names_disjointE //.
  by rewrite renamevE renamepE /= (names_disjointE disvs).
rewrite (_ : pm i |: _ = pm @: (i |: names (v :: vs))); last first.
  by rewrite imfsetU1 -names_rename renamesE.
set A := pm @: (i |: _).
move: (fresh _) (freshP A)=> n ninA /=.
rewrite /new -!lock /=.
rewrite rename_stateu rename_blockat renamesE /=.
rewrite [rename pm (VPtr _)]renamevE renamepE /= renameT.
by rewrite renameKV IH // renamenE fpermKV.
Qed.

End Logic.
