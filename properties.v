From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype choice seq ssrnum ssrint ssralg bigop.

From CoqUtils Require Import ord fset partmap fperm nominal string.

Require Import basic.

Require structured.

Module str := structured.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Properties.

Local Open Scope fset_scope.

Local Notation state := (locals * heap)%type.

Implicit Type (e : expr) (c : com) (ls : locals) (h : heap)
              (s : state) (π : {fperm name}) (v : value).

Definition stateu s1 s2 := (unionm s1.1 s2.1, unionm s1.2 s2.2).

Local Infix "∪" := stateu (at level 40, left associativity).

Lemma rename_stateu π s1 s2 : rename π (s1 ∪ s2) = rename π s1 ∪ rename π s2.
Proof. by rewrite /stateu renamepE /= !renamem_union. Qed.

Local Notation eval_com := (eval_com (basic_sem true)).

Definition vars_s s := domm s.1.

Definition objs s := names (domm s.2).

Lemma rename_objs π s : rename π (objs s) = objs (rename π s).
Proof.
by case: s=> ls h; rewrite /objs -renamem_dom /= names_rename.
Qed.

Lemma objs_names s : fsubset (objs s) (names s).
Proof.
rewrite /objs.
apply: (@equivariant_names _ _ (fun s => domm s.2)).
by move=> /= π [ls h] /=; rewrite renamem_dom.
Qed.

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

Lemma vars_sE A s : vars_s s = str.vars_s (mask A s).
Proof. by case: s=> ??; rewrite str.vars_sE. Qed.

Lemma rename_vars_s π s : vars_s (rename π s) = vars_s s.
Proof.
case: s=> ls h; rewrite renamepE /= /vars_s /= -renamem_dom.
by rewrite renameT.
Qed.

Lemma stateuE A1 s1 A2 s2 :
  mutfresh A1 s1 A2 s2 ->
  str.stateu (mask A1 s1) (mask A2 s2) =
  mask (A1 :|: A2) (s1 ∪ s2).
Proof. case: s1 s2=> [??] [??]; exact: str.stateuE. Qed.

Lemma pubE A s : str.pub (mask A s) = objs s :\: A.
Proof. by case: s; apply: str.pubE. Qed.

Lemma restr_eval_com_vars s s' c k :
  fsubset (vars_c c) (vars_s s) ->
  eval_com s c k = Done s' ->
  vars_s s' = vars_s s.
Proof.
have [A ev sub ev'] := str.eval_basic_restr fset0 s c k.
move: ev; rewrite ev' (vars_sE A) (vars_sE fset0).
by apply: str.restr_eval_com_vars; rewrite -vars_sE.
Qed.

Lemma renaming π s c k :
  exists π',
    eval_com (rename π s) c k =
    rename π' (eval_com s c k).
Proof.
have [A1 eA1] := str.eval_basic_restr (names s) s c k.
have [A2 eA2] := str.eval_basic_restr (names (rename π s)) (rename π s) c k.
move: eA2; rewrite names_rename -renamefsE -renamerE -str.renaming {}eA1.
case: eval_com => [s1'| |]; case: eval_com => //;
try by exists 1%fperm; rewrite rename1.
move=> s2' []; rewrite renamerE => /mask_eqP /= [π' _ [_ <-]].
by exists (π' * π)%fperm; rewrite renameD.
Qed.

Theorem frame_ok s1 s1' s2 c k :
  fsubset (vars_c c) (vars_s s1) ->
  fdisjoint (vars_s s1) (vars_s s2) -> (* This should not be necessary *)
  fdisjoint (objs s1) (objs s2) ->
  eval_com s1 c k = Done s1' ->
  exists2 π,
    eval_com (s1 ∪ s2) c k = Done (rename π s1' ∪ s2)
    & fdisjoint (objs (rename π s1')) (objs s2).
Proof.
move=> sub dis_v dis_o ev.
rewrite -(restr_eval_com_vars sub ev) in dis_v.
have [A] := str.eval_basic_restr fset0 s1 c k; rewrite ev [mask A _]maskI.
move: (_ :&: _) (fsubsetIr A (names s1'))=> /= {A} A subA ev'.
rewrite (vars_sE fset0) in sub.
have dis' : fdisjoint (str.pub (mask fset0 s1)) (str.pub (mask fset0 s2)).
  by rewrite !pubE !fsetD0.
have {sub dis'} := str.frame_ok sub dis' ev'.
rewrite stateuE ?/mutfresh ?fdisjoint0 // fsetU0 => ev''.
have [A'] := str.eval_basic_restr fset0 (s1 ∪ s2) c k.
rewrite ev''; case: eval_com=> // s' [] es'.
move: es' ev''; rewrite [mask A' _]maskI.
move: (_ :&: _) (fsubsetIr A' (names s'))=> /= {A'} A' subA'.
move e: (mask A s1') => /= s1''.
case/(restrP (names s2)): s1'' e => /= A'' s1'' disA'' subA''.
rewrite stateuE ?fsetU0 /mutfresh 1?fdisjointC ?disA'' ?fdisjoint0 //.
case/mask_eqP=> /= π dis_π; rewrite (fsetIidPl _ _ subA'').
rewrite (fsetIidPl _ _ subA).
rewrite -{2 3}(renameK π s1').
rewrite -namesrE in dis_π.
move: (dis_π) subA ev' dis_o.
rewrite (renamefs_subset π) (renamefsE _ (names s1')) -names_rename.
rewrite -[mask A s1'](@names_disjointE _ π) // renamerE.
move: dis_v; rewrite -(rename_vars_s π s1').
move: (rename π A) (rename π s1') => {A s1' dis_π ev} /= A s1' dis_v _ subA ev.
move=> dis [e1 e2]; move: disA'' {subA''}; rewrite -{}e1 -{}e2 {A'' s1''}.
move=> dis_πA; case/mask_eqP=> /= π' dis_π'.
rewrite (fsetIidPl _ _ subA').
move=> [_ <-] {A' s' subA'} ev'.
have dis_s1' : fdisjoint (objs s1') (objs s2).
  have sub: fsubset (objs s1') (A :|: objs s1).
    rewrite -fsubDset -pubE -[objs s1]fsetD0 -pubE.
    by apply: str.restr_eval_com_pub; eauto.
  apply: fdisjoint_trans; eauto.
  rewrite fdisjointUl dis andbT fdisjointC.
  apply: fdisjoint_trans; last by eauto.
  exact: objs_names.
have e_s2 : rename π' s2 = s2.
  rewrite names_stateu // in dis_π'.
  rewrite names_disjointE //.
  move: dis_π'; rewrite fsetDUl fdisjointUr=>/andP [_].
  by move/fsetDidPl: dis_πA => ->.
exists (π' * π)%fperm; rewrite ?rename_stateu renameD fperm_mulsK {π}.
  by congr Done; congr stateu.
by rewrite -e_s2 -!rename_objs -renamefs_disjoint.
Qed.

Theorem frame_loop s1 s2 c k :
  fsubset (vars_c c) (vars_s s1) ->
  fdisjoint (objs s1) (objs s2) ->
  eval_com s1 c k = NotYet ->
  eval_com (s1 ∪ s2) c k = NotYet.
Proof.
move=> sub dis ev.
have e_vars_s : vars_s s1 = str.vars_s (mask fset0 s1).
  by case: (s1)=> ??; rewrite str.vars_sE.
rewrite e_vars_s in sub.
have [A] := str.eval_basic_restr fset0 s1 c k; rewrite ev {A}.
move=> ev'.
have dis' : fdisjoint (str.pub (mask fset0 s1)) (str.pub (mask fset0 s2)).
  by rewrite !pubE !fsetD0.
have ev'' := str.frame_loop sub dis' ev'.
have [A] := str.eval_basic_restr fset0 (s1 ∪ s2) c k.
rewrite stateuE ?fset0U in ev''; last by rewrite /mutfresh !fdisjoint0.
by rewrite ev''; case: eval_com.
Qed.

Theorem frame_error s1 s2 c k :
  fsubset (vars_c c) (vars_s s1) ->
  fdisjoint (names s1) (objs s2) ->
  eval_com s1 c k = Error ->
  eval_com (s1 ∪ s2) c k = Error.
Proof.
move=> sub dis ev.
have e_vars_s : vars_s s1 = str.vars_s (mask fset0 s1).
  by case: (s1)=> ??; rewrite str.vars_sE.
rewrite e_vars_s in sub.
have [A] := str.eval_basic_restr fset0 s1 c k; rewrite ev {A}.
move=> ev'.
have dis' : fdisjoint (names (mask fset0 s1)) (str.pub (mask fset0 s2)).
  by rewrite namesrE !pubE !fsetD0.
have ev'' := str.frame_error sub dis' ev'.
have [A] := str.eval_basic_restr fset0 (s1 ∪ s2) c k.
rewrite stateuE ?fset0U in ev''; last by rewrite /mutfresh !fdisjoint0.
by rewrite ev''; case: eval_com.
Qed.

Corollary noninterference s1 s21 s' s22 c k :
  fsubset (vars_c c) (vars_s s1) ->
  fdisjoint (vars_s s1) (vars_s s21) -> (* Same applies here *)
  fdisjoint (vars_s s1) (vars_s s22) -> (* And here *)
  fdisjoint (names s1) (objs s21) ->
  fdisjoint (objs s1) (objs s22) ->
  eval_com (s1 ∪ s21) c k = Done s' ->
  exists s1' π1 π2,
    [/\ eval_com s1 c k = Done s1',
        s' = rename π1 s1' ∪ s21,
        fdisjoint (objs (rename π1 s1')) (objs s21),
        eval_com (s1 ∪ s22) c k = Done (rename π2 s1' ∪ s22) &
        fdisjoint (objs (rename π2 s1')) (objs s22) ].
Proof.
move=> sub dis_v1 dis_v2 dis_o1 dis_o2 eval_c.
have dis_o1' : fdisjoint (objs s1) (objs s21).
  apply: fdisjoint_trans; last exact: dis_o1.
  exact: objs_names.
case eval_c': (eval_com s1 c k) => [s1'| |] //=.
- exists s1'.
  have [π1 eπ1 disπ1] := frame_ok sub dis_v1 dis_o1' eval_c'.
  exists π1; move: eπ1; rewrite eval_c => - [->].
  have [π2 eπ2 disπ2] := frame_ok sub dis_v2 dis_o2 eval_c'.
  by exists π2; split.
- by rewrite (frame_error sub dis_o1 eval_c') in eval_c.
by rewrite (frame_loop sub _ eval_c') // in eval_c.
Qed.

End Properties.
