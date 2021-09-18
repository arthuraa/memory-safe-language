Require Import Coq.Strings.String.

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype choice seq ssrnum ssrint ssralg bigop.
From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun fperm.

From CoqUtils Require Import nominal.

From memsafe Require Import basic.

From memsafe Require structured.

Module str := structured.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Properties.

Local Open Scope fset_scope.
Local Open Scope state_scope.

Local Notation locals := {fmap string -> value}.
Local Notation heap := {fmap ptr -> value}.
Local Notation state := (locals * heap)%type.

Implicit Type (e : expr) (c : com) (ls : locals) (h : heap)
              (s : state) (π : {fperm name}) (v : value).

Definition vars_s s := domm s.1.

Definition objs s := names (domm s.2).

Instance vars_s_eqvar : {eqvar vars_s}.
Proof. by rewrite /vars_s; finsupp. Qed.

Instance objs_eqvar : {eqvar objs}.
Proof. by rewrite /objs; finsupp. Qed.

Lemma objs_names s : fsubset (objs s) (names s).
Proof. eapply nom_finsuppP; finsupp. Qed.

Lemma objsU s1 s2 : objs (s1 ∪ s2) = objs s1 :|: objs s2.
Proof.
case: s1 s2=> /= [ls1 h1] [ls2 h2].
by rewrite /stateu /objs /= domm_union namesfsU.
Qed.

Lemma names_stateu s1 s2 :
  fdisjoint (vars_s s1) (vars_s s2) ->
  fdisjoint (objs s1) (objs s2) ->
  names (s1 ∪ s2) = names s1 :|: names s2.
Proof.
case: s1 s2 => /= [ls1 h1] [ls2 h2].
rewrite /vars_s /objs /stateu !namespE /= => dis_v dis_o.
rewrite namesm_union_disjoint // namesm_union_disjoint.
  rewrite 2!fsetUA; congr fsetU.
  by rewrite -2!fsetUA [_ :|: names h1]fsetUC.
by apply: fdisjoint_names_domm.
Qed.

Lemma vars_sE A s : vars_s s = expose (mapr fset0 vars_s (hide A (Restr s))).
Proof. by rewrite /vars_s maprE ?fdisjoint0s ?exposeE. Qed.

Lemma renaming π s c k :
  exists π',
    eval_com true c (rename π s) k =
    rename π' (eval_com true c s k).
Proof.
have [A1 eA1] := str.eval_basic_restr c s k.
have [A2 eA2] := str.eval_basic_restr c (rename π s) k.
move: eA2; rewrite -str.eval_com_eqvar {}eA1.
case: eval_com => [s1'| |]; case: eval_com => //;
try by exists 1%fperm; rewrite rename1.
move=> s2' []; rewrite hide_eqvar Restr_eqvar  => /restr_eqP /= [π' _ [_ <-]].
by exists (π' * π)%fperm; rewrite renameA.
Qed.

Theorem frame_ok s1 s1' s2 c k :
  fsubset (vars_c c) (vars_s s1) ->
  fdisjoint (vars_s s1) (vars_s s2) -> (* This should not be necessary *)
  fdisjoint (objs s1) (objs s2) ->
  eval_com true c s1 k = Done s1' ->
  exists2 π,
    eval_com true c (s1 ∪ s2) k = Done (rename π s1' ∪ s2)
    & fdisjoint (objs (rename π s1')) (objs s2).
Proof.
move=> sub dis_v dis_o ev.
rewrite /vars_s -(eval_com_vars sub ev) in dis_v.
have [A] := str.eval_basic_restr c s1 k; rewrite ev hideI namesrE.
move: (_ :&: _) (fsubsetIr A (names s1'))=> /= {A} A subA ev'.
have {sub} ev'' := str.frame_ok sub dis_o ev'.
have [A'] := str.eval_basic_restr c (s1 ∪ s2) k.
rewrite ev''; case: eval_com=> // s' [] es'.
move: es' ev''; rewrite [hide A' _]hideI namesrE.
move: (_ :&: _) (fsubsetIr A' (names s'))=> /= {A'} A' subA'.
move e: (hide A (Restr s1')) => /= s1''.
case/(restrP (names s1 :|: names s2)): s1'' e => /= A'' s1'' disA'' subA''.
move: disA''; rewrite fdisjointUl=> /andP [dis_s1_A'' dis_s2_A''].
rewrite maprE //.
case/restr_eqP=> /= π dis_π; rewrite (fsetIidPl subA'').
rewrite (fsetIidPl subA).
rewrite -{2 3}(renameK π s1').
rewrite -namesrE in dis_π.
move: (dis_π) subA ev' dis_o.
rewrite -[fsubset _ _](renameT π) fsubset_eqvar (renamefsE _ (names s1')) -names_rename.
rewrite -[hide A _](@renameJ _ π) // ?names_hider // hide_eqvar Restr_eqvar.
move: dis_v; rewrite -[domm s1'.1](renameT π) domm_eqvar fst_eqvar.
move: (rename π A) (rename π s1') => {A s1' dis_π ev} /= A s1' dis_v _ subA ev.
move=> dis [e1 e2]; move: dis_s1_A'' dis_s2_A'' {subA''}.
rewrite -{}e1 -{}e2 {A'' s1''}.
move=> dis_s1_A dis_s2_A; case/restr_eqP=> /= π' dis_π'.
rewrite (fsetIidPl subA').
move=> [_ <-] {A' s' subA'} ev'.
have dis_s1' : fdisjoint (objs s1') (objs s2).
  have:= @str.eval_com_blocks (objs s2) s1 c k dis.
  rewrite ev /= str.pbind_resE.
  have: fdisjoint (names (objs s2)) A.
    by apply: fdisjoint_trans dis_s2_A; eapply nom_finsuppP; finsupp.
  move: (objs s2) => A' disA'.
  by rewrite pbindrE //= namesfsnE.
have e_s2 : rename π' s2 = s2.
  rewrite names_stateu // in dis_π'.
  rewrite renameJ //.
  move: dis_π'; rewrite fsetDUl fdisjointUr=>/andP [_].
  by move/fsetDidPl: dis_s2_A => ->.
exists (π' * π)%fperm; rewrite ?stateu_eqvar renameA fperm_mulsK {π}.
  by congr Done; congr stateu.
by rewrite -e_s2 -objs_eqvar -[objs (rename _ _)]objs_eqvar -fdisjoint_eqvar.
Qed.

Theorem frame_loop s1 s2 c k :
  fsubset (vars_c c) (vars_s s1) ->
  fdisjoint (objs s1) (objs s2) ->
  eval_com true c s1 k = NotYet ->
  eval_com true c (s1 ∪ s2) k = NotYet.
Proof.
move=> sub dis ev.
have [A] := str.eval_basic_restr c s1 k; rewrite ev {A}.
move=> ev'.
have ev'' := str.frame_loop sub dis ev'.
have [A] := str.eval_basic_restr c (s1 ∪ s2) k.
by rewrite ev''; case: eval_com.
Qed.

Theorem frame_error s1 s2 c k :
  fsubset (vars_c c) (vars_s s1) ->
  fdisjoint (names s1) (objs s2) ->
  eval_com true c s1 k = Error ->
  eval_com true c (s1 ∪ s2) k = Error.
Proof.
move=> sub dis ev.
have [A] := str.eval_basic_restr c s1 k; rewrite ev {A}.
move=> ev'.
have ev'' := str.frame_error sub dis ev'.
have [A] := str.eval_basic_restr c (s1 ∪ s2) k.
by rewrite ev''; case: eval_com.
Qed.

Corollary noninterference s1 s21 s' s22 c k :
  fsubset (vars_c c) (vars_s s1) ->
  fdisjoint (vars_s s1) (vars_s s21) -> (* Same applies here *)
  fdisjoint (vars_s s1) (vars_s s22) -> (* And here *)
  fdisjoint (names s1) (objs s21) ->
  fdisjoint (objs s1) (objs s22) ->
  eval_com true c (s1 ∪ s21) k = Done s' ->
  exists s1' π1 π2,
    [/\ eval_com true c s1 k = Done s1',
        s' = rename π1 s1' ∪ s21,
        fdisjoint (objs (rename π1 s1')) (objs s21),
        eval_com true c (s1 ∪ s22) k = Done (rename π2 s1' ∪ s22) &
        fdisjoint (objs (rename π2 s1')) (objs s22) ].
Proof.
move=> sub dis_v1 dis_v2 dis_o1 dis_o2 eval_c.
have dis_o1' : fdisjoint (objs s1) (objs s21).
  apply: fdisjoint_trans; last exact: dis_o1.
  exact: objs_names.
case eval_c': (eval_com true c s1 k) => [s1'| |] //=.
- exists s1'.
  have [π1 eπ1 disπ1] := frame_ok sub dis_v1 dis_o1' eval_c'.
  exists π1; move: eπ1; rewrite eval_c => - [->].
  have [π2 eπ2 disπ2] := frame_ok sub dis_v2 dis_o2 eval_c'.
  by exists π2; split.
- by rewrite (frame_error sub dis_o1 eval_c') in eval_c.
by rewrite (frame_loop sub _ eval_c') // in eval_c.
Qed.

End Properties.
