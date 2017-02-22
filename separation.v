From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.

From CoqUtils Require Import ord fset partmap fperm nominal string.

Require Import basic properties.

Require structured.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Separation.

Local Open Scope fset_scope.

Local Notation state := (locals * heap)%type.

Implicit Type (e : expr) (c : com) (ls : locals) (h : heap)
              (s : state) (π : {fperm name}) (v : value)
              (P Q R : state -> Prop).

Local Notation eval_com_b := (eval_com (basic_sem true)).
Local Notation eval_com_s := (eval_com structured.restr_sem).

Definition lift_restr P rs :=
  forall A s, rs = mask A s -> P s.

Lemma lift_restrP P A s :
  lift_restr P (mask A s) <->
  (forall π, fdisjoint (supp π) (names s :\: A) -> P (rename π s)).
Proof.
split.
  move=> h π dis; apply: (h (rename π A)).
  apply/mask_eqP; exists π=> //.
  by rewrite renamefsI names_rename.
move=> h A' s' /mask_eqP /= [π dis [e <-]].
by apply: h.
Qed.

Definition triple P c Q :=
  forall s k, fsubset (vars_c c) (vars_s s) ->
              P s ->
              match eval_com_s (mask fset0 s) c k with
              | Done rs' => lift_restr Q rs'
              | Error    => False
              | NotYet   => True
              end.

Definition separating_conjunction P Q s :=
  exists ls h1 h2,
    [/\ s = (ls, unionm h1 h2),
        P (ls, h1),
        Q (ls, h2) &
        fdisjoint (objs (ls, h1)) (objs (ls, h2)) ].

Local Infix "*" := separating_conjunction.

Definition ind_vars (xs : {fset string}) P :=
  forall s s', P s ->
               (forall x, x \notin xs -> s.1 x = s'.1 x) ->
               P s'.

Lemma sc_lift P Q A ls h1 h2 :
  lift_restr P (mask A (ls, h1)) ->
  lift_restr Q (mask A (ls, h2)) ->
  fdisjoint (names (domm h1)) (names (domm h2)) ->
  lift_restr (P * Q) (mask A (ls, unionm h1 h2)).
Proof.
move=> /lift_restrP Ph1 /lift_restrP Qh2 dis.
apply/lift_restrP=> π.
rewrite fsetDUl /= namesm_union_disjoint ?fdisjoint_names_domm //.
rewrite (fsetDUl (names h1)) -[names ls :\: A]fsetUid -fsetUA.
rewrite [in X in _ :|: X]fsetUC 2!fsetUA -fsetUA (fsetUC (names h2 :\: A)).
rewrite -2!fsetDUl -(namespE (ls, h1)) -(namespE (ls, h2)) fdisjointUr.
case/andP=> [dis_π1 dis_π2].
exists (rename π ls), (rename π h1), (rename π h2).
rewrite renamepE /= renamem_union; split=> //.
- by apply: Ph1.
- by apply: Qh2.
by rewrite /objs /= -2!renamem_dom !names_rename -renamefs_disjoint.
Qed.

Lemma frame_rule P Q R c :
  triple P c Q ->
  ind_vars (mod_vars_c c) R ->
  triple (P * R) c (Q * R).
Proof.
move=> t ind s k sub [ls [h1 [h2 [e ph1 ph2 dis]]]].
rewrite {}e {s} in sub *.
rewrite -[ls]unionm0 -[fset0]fset0U -str.stateuE /mutfresh ?fdisjoint0 //.
move/(_ (ls, h1) k sub ph1): t.
have {sub} sub : fsubset (vars_c c) (str.vars_s (mask fset0 (ls, h1))).
  by rewrite -vars_sE.
have dis' : fdisjoint (str.pub (mask fset0 (ls, h1)))
                      (str.pub (mask fset0 (emptym, h2))).
  by rewrite !pubE !fsetD0.
case ev: (eval_com_s (mask fset0 (ls, h1)) c k)=> [rs'| |] //=; first last.
  by rewrite (str.frame_loop sub dis' ev).
move=> Q_rs'; rewrite (str.frame_ok sub dis' ev).
case: rs' / (restrP (names ((emptym, h2) : state)) rs') Q_rs' ev
      => /= A [ls' h1'] dis'' sub' Q_rs' ev.
rewrite str.stateuE /mutfresh ?fdisjoint0 1?fdisjointC ?dis'' // fsetU0 unionm0.
rewrite namespE /= namesm_empty fset0U in dis''.
apply: sc_lift=> //.
  apply/lift_restrP=> π.
  rewrite namespE fsetDUl /= (fsetDidPl _ _ dis'') fdisjointUr.
  case/andP=> dis_ls' dis_h2.
  rewrite renamepE /= (names_disjointE dis_h2).
  apply/ind; eauto=> /= x nin_x.
  pose f (st : state) := st.1 x.
  have eq_f : equivariant f.
    by move=> ? [??]; rewrite /f !renamepE /= renamemE renameT.
  have e : oexpose (mapr f (mask fset0 (ls, h1))) = Some (ls x).
    by rewrite maprE // /f /= oexposeE fdisjoint0.
  rewrite -(str.mod_vars_cP ev nin_x) maprE //= oexposeE in e.
  case: ifP e=> // dis''' [<-].
  rewrite renamemE renameT names_disjointE // fdisjointC.
  rewrite fdisjointC in dis_ls'.
  apply/fdisjoint_trans; eauto.
  apply/fsubsetP=> /= i in_i; apply/fsetDP; split.
    case e: getm in_i=> [v|]; try by rewrite in_fset0.
    move=> in_i; apply/namesmP/@PMFreeNamesVal; eauto.
  by move: i in_i; apply/fdisjointP; rewrite fdisjointC.
suffices ?: fsubset (names (domm h1')) (names (domm h1) :|: A).
  apply: fdisjoint_trans; eauto.
  rewrite fdisjointUl dis /= fdisjointC.
  apply: fdisjoint_trans; eauto.
  apply: equivariant_names.
  by move=> ??; rewrite renamem_dom.
rewrite fsetUC -fsubDset -[names (domm h1')]/(objs (ls', h1')).
rewrite  -[names (domm h1)]/(objs (ls, h1)) -[objs (ls, h1)]fsetD0 -!pubE.
apply: str.restr_eval_com_pub; eauto.
Qed.

End Separation.
