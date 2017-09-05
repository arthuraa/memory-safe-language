From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.

From CoqUtils Require Import ord fset partmap fperm nominal string.

Require Import basic structured.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Separation.

Local Open Scope fset_scope.
Local Open Scope state_scope.

Local Notation locals := {partmap string -> value}.
Local Notation heap := {partmap ptr -> value}.
Local Notation state := (locals * heap)%type.

Implicit Type (e : expr) (c : com) (ls : locals) (h : heap)
              (s : state) (π : {fperm name}) (v : value)
              (P Q R : state -> Prop).

Definition triple P c Q :=
  forall s k, fsubset (vars_c c) (domm s.1) ->
              P s ->
              match eval_com c s k with
              | Done rs' => pbindr fset0 Q rs'
              | Error    => False
              | NotYet   => True
              end.

Definition separating_conjunction P Q s :=
  exists ls h1 h2,
    [/\ s = (ls, unionm h1 h2),
        P (ls, h1),
        Q (ls, h2) &
        fdisjoint (names (domm h1)) (names (domm h2)) ].

Local Infix "*" := separating_conjunction.

Definition ind_vars (xs : {fset string}) P :=
  forall s s', P s ->
               (forall x, x \notin xs -> s.1 x = s'.1 x) ->
               s.2 = s'.2 ->
               P s'.

Lemma sc_lift P Q A ls h1 h2 :
  pbindr fset0 P (hide A (Restr (ls, h1))) ->
  pbindr fset0 Q (hide A (Restr (ls, h2))) ->
  fdisjoint (names (domm h1)) (names (domm h2)) ->
  pbindr fset0 (P * Q) (hide A (Restr (ls, unionm h1 h2))).
Proof.
move=> Ph1 Qh2 dis A12 /= s /restr_eqP /= [π ids_π [eA es]] _.
move: ids_π.
rewrite fsetDUl /= namesm_union_disjoint ?fdisjoint_names_domm //.
rewrite (fsetDUl (names h1)) -[names ls :\: A]fsetUid -fsetUA.
rewrite [in X in _ :|: X]fsetUC 2!fsetUA -fsetUA (fsetUC (names h2 :\: A)).
rewrite -2!fsetDUl -(namespE (ls, h1)) -(namespE (ls, h2)) fdisjointUr.
case/andP=> [dis_π1 dis_π2].
exists (rename π ls), (rename π h1), (rename π h2).
rewrite -es pair_eqvar unionm_eqvar; split=> //.
- apply: (Ph1 (rename π A)); last exact: fdisjoint0s.
  rewrite -[LHS](@renameJ _ π) ?names_hider ?namesrE //.
  by rewrite hide_eqvar Restr_eqvar pair_eqvar.
- apply: (Qh2 (rename π A)); last exact: fdisjoint0s.
  rewrite -[LHS](@renameJ _ π) ?names_hider ?namesrE //.
  by rewrite hide_eqvar Restr_eqvar pair_eqvar.
by rewrite -![domm (rename _ _)]domm_eqvar -fdisjoint_eqvar renameT.
Qed.

Lemma frame_rule P Q R c :
  triple P c Q ->
  ind_vars (mod_vars_c c) R ->
  triple (P * R) c (Q * R).
Proof.
move=> t ind s k sub [ls [h1 [h2 [e ph1 ph2 dis]]]].
rewrite {}e {s} in sub *.
move/(_ (ls, h1) k sub ph1): t.
rewrite -{2}[ls]unionm0.
case ev: (eval_com c (ls, h1) k)=> [rs'| |] //=; first last.
  by rewrite (@frame_loop _ (ls, h1) (emptym, h2)).
move=> Q_rs'; rewrite (@frame_ok _ (ls, h1) (emptym, h2) _ _ sub dis ev).
case: rs' / (restrP (names (ls, h1) :|: names ((emptym, h2) : state)) rs')
          Q_rs' ev => /= A [ls' h1'] dis'' sub' Q_rs' ev.
move: dis''; rewrite fdisjointUl=> /andP [dis1 dis2].
rewrite maprE // /stateu unionm0.
rewrite namespE /= namesm_empty fset0U in dis2.
apply: sc_lift=> //.
  move=> /= A' s2' /restr_eqP [π].
  rewrite namespE fsetDUl /= (fsetDidPl _ _ dis2) fdisjointUr.
  case/andP=> dis_ls' dis_h2.
  rewrite pair_eqvar /= (renameJ dis_h2) => - [eA <-] _.
  apply/ind; eauto=> /= x nin_x.
  move: (mod_vars_cP ev nin_x); rewrite maprE ?fdisjoint0s //=.
  move/(congr1 (@oexpose _)); rewrite oexposeE oexposeE0.
  case: ifP=> // dis''' [<-].
  rewrite renamemE renameT renameJ // fdisjointC.
  rewrite fdisjointC in dis_ls'.
  apply/fdisjoint_trans; eauto.
  apply/fsubsetP=> /= i in_i; apply/fsetDP; split.
    case e: getm in_i=> [v|]; try by rewrite in_fset0.
    move=> in_i; apply/namesmP/@PMFreeNamesVal; eauto.
  by move: i in_i; apply/fdisjointP; rewrite fdisjointC.
have := @eval_com_blocks _ (ls, h1) c k dis.
rewrite ev pbind_resE /=.
have: fdisjoint (names (domm h2)) A.
  by apply: fdisjoint_trans dis2; eapply nom_finsuppP; finsupp.
move: (names (domm h2)) => A' disA'.
by rewrite pbindrE //= namesfsnE.
Qed.

Definition weak_triple P c Q :=
  forall s k,
    fsubset (vars_c c) (domm s.1) ->
    P s ->
    if eval_com c s k is Done rs' then
      pbindr fset0 Q rs'
    else True.

Definition strong_separating_conjunction P Q s :=
  exists ls h1 h2,
    [/\ s = (ls, unionm h1 h2),
        P (ls, h1),
        Q (ls, h2) &
        fdisjoint (names (ls, h1)) (names (domm h2)) ].

Local Infix "*>" := strong_separating_conjunction (at level 20).

Lemma ssc_lift P Q A ls h1 h2 :
  pbindr fset0 P (hide A (Restr (ls, h1))) ->
  pbindr fset0 Q (hide A (Restr (ls, h2))) ->
  fdisjoint (names (ls, h1)) (names (domm h2)) ->
  pbindr fset0 (P *> Q) (hide A (Restr (ls, unionm h1 h2))).
Proof.
move=> Ph1 Qh2 dis A12 /= s /restr_eqP /= [π ids_π [eA es]] _.
move: ids_π.
rewrite fsetDUl /= namesm_union_disjoint ?fdisjoint_names_domm //; last first.
  suffices h : fsubset (names (domm h1)) (names (ls, h1)).
    by apply: fdisjoint_trans; eauto.
  by rewrite fsubsetU //= [_ _ (names h1)]fsubsetU ?orbT ?fsubsetxx.
rewrite (fsetDUl (names h1)) -[names ls :\: A]fsetUid -fsetUA.
rewrite [in X in _ :|: X]fsetUC 2!fsetUA -fsetUA (fsetUC (names h2 :\: A)).
rewrite -2!fsetDUl -(namespE (ls, h1)) -(namespE (ls, h2)) fdisjointUr.
case/andP=> [dis_π1 dis_π2].
exists (rename π ls), (rename π h1), (rename π h2).
rewrite -es pair_eqvar unionm_eqvar; split=> //.
- apply: (Ph1 (rename π A)); last exact: fdisjoint0s.
  rewrite -[LHS](@renameJ _ π) ?names_hider ?namesrE //.
  by rewrite hide_eqvar Restr_eqvar pair_eqvar.
- apply: (Qh2 (rename π A)); last exact: fdisjoint0s.
  rewrite -[LHS](@renameJ _ π) ?names_hider ?namesrE //.
  by rewrite hide_eqvar Restr_eqvar pair_eqvar.
by rewrite -![domm (rename _ _)]domm_eqvar -fdisjoint_eqvar renameT.
Qed.

Lemma weak_frame_rule P Q R c :
  weak_triple P c Q ->
  ind_vars (mod_vars_c c) R ->
  weak_triple (P *> R) c (Q *> R).
Proof.
move=> t ind s k sub [ls [h1 [h2 [e ph1 ph2 dis]]]].
rewrite {}e {s} in sub *.
move/(_ (ls, h1) k sub ph1): t.
rewrite -{2}[ls]unionm0.
have dis': fdisjoint (names (domm h1)) (names (domm h2)).
  move: dis; rewrite fdisjointUl=> /andP [_] /=.
  by rewrite fdisjointUl=> /andP [].
case ev: (eval_com c (ls, h1) k)=> [rs'| |] //=; first last.
- by rewrite (@frame_loop _ (ls, h1) (emptym, h2)).
- by rewrite (@frame_error _ (ls, h1) (emptym, h2)).
move=> Q_rs'; rewrite (@frame_ok _ (ls, h1) (emptym, h2) _ _ sub dis' ev).
case: rs' / (restrP (names (ls, h1) :|: names ((emptym, h2) : state)) rs')
          Q_rs' ev => /= A [ls' h1'] dis'' sub' Q_rs' ev.
move: dis''; rewrite fdisjointUl=> /andP [dis1 dis2].
rewrite maprE // /stateu unionm0.
rewrite namespE /= namesm_empty fset0U in dis2.
apply: ssc_lift=> //.
  move=> /= A' s2' /restr_eqP [π].
  rewrite namespE fsetDUl /= (fsetDidPl _ _ dis2) fdisjointUr.
  case/andP=> dis_ls' dis_h2.
  rewrite pair_eqvar /= (renameJ dis_h2) => - [eA <-] _.
  apply/ind; eauto=> /= x nin_x.
  move: (mod_vars_cP ev nin_x); rewrite maprE ?fdisjoint0s //=.
  move/(congr1 (@oexpose _)); rewrite oexposeE oexposeE0.
  case: ifP=> // dis''' [<-].
  rewrite renamemE renameT renameJ // fdisjointC.
  rewrite fdisjointC in dis_ls'.
  apply/fdisjoint_trans; eauto.
  apply/fsubsetP=> /= i in_i; apply/fsetDP; split.
    case e: getm in_i=> [v|]; try by rewrite in_fset0.
    move=> in_i; apply/namesmP/@PMFreeNamesVal; eauto.
  by move: i in_i; apply/fdisjointP; rewrite fdisjointC.
have: fsubset (names (eval_com c (ls, h1) k)) (names (ls, h1)).
  eapply nom_finsuppP; finsupp.
rewrite ev namesresE names_hider namesrE fsubDset fsetUC => ?.
apply: fdisjoint_trans; first eauto.
rewrite fdisjointUl dis fdisjointC.
apply: fdisjoint_trans; eauto.
by eapply nom_finsuppP; finsupp.
Qed.

End Separation.
