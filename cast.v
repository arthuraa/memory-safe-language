From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype choice seq ssrnum ssrint ssralg bigop.

From CoqUtils Require Import ord fset partmap fperm nominal string.

Require Import basic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Cast.

Local Open Scope fset_scope.

Lemma eval_com_domm safe ls h ls' h' c k :
  fsubset (vars_c c) (domm ls) ->
  eval_com (basic_sem safe) (ls, h) c k = Done (ls', h') ->
  domm ls' = domm ls.
Proof.
elim: k ls ls' h h' c => [|k IH] //= ls ls' h h'.
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=.
- rewrite fsubU1set=> /andP [Px Pe] [<- _]; rewrite domm_set.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsubsetUr.
- case: eval_expr => // p; case: (h p)=> [v|] //=.
  rewrite fsubU1set=> /andP [Px Pe] [<- _]; rewrite domm_set.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsubsetUr.
- case: eval_expr => // p; rewrite /updm; case: (h p)=> [v|] //=.
  by rewrite fsubUset=> /andP [Pe Pe'] [<- _].
- case: eval_expr => // - [n|] //.
  rewrite fsubU1set=> /andP [Px Pe] [<- _]; rewrite domm_set.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsubsetUr.
- case: eval_expr => // p.
  by have [|]:= altP eqP=> // _; case: free_fun=> // h'' _ [<- _].
- congruence.
- case eval_c1: eval_com=> [[ls'' h'']| | ] //.
  rewrite fsubUset=> /andP [vars_c1 vars_c2] eval_c2.
  rewrite -(IH _ _ _ _ _ vars_c1 eval_c1) in vars_c2 *.
  by rewrite (IH _ _ _ _ _ vars_c2 eval_c2).
- case: eval_expr=> // - b.
  by rewrite 2!fsubUset -andbA => /and3P [_ vars_c1 vars_c2]; case: b; eauto.
case: eval_expr=> // - [] P; apply: IH.
  by rewrite /= fsetUC -fsetUA fsetUid.
by rewrite fsub0set.
Qed.

Theorem weak_frame ls1 h1 ls2 h2 ls' h' safe c k :
  fsubset (vars_c c) (domm ls1) ->
  fdisjoint (domm ls1) (domm ls2) ->
  fdisjoint (names (ls1, h1)) (names (domm h2)) ->
  eval_com (basic_sem safe) (unionm ls1 ls2, unionm h1 h2) c k =
  Done (ls', h') ->
  exists ls1' h1',
    [/\ ls' = unionm ls1' ls2,
        h'  = unionm h1' h2,
        fdisjoint (domm ls1') (domm ls2) &
        fsubset (names (ls1', h1') :&: (names h2))
                (names (ls1, h1))].
Proof.
elim: k ls1 h1 ls' h' c=> [//=|k IH] ls1 h1 ls' h' c.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=.
- (* Assn *)
  rewrite fsubU1set=> /andP [Px sub] disl dish [<- <-].
  rewrite setm_union; do 3!eexists; eauto.
    by rewrite domm_set; apply/fdisjointP=> x' /fsetU1P [->|];
    move/fdisjointP: disl; apply.
  rewrite fsetIUl fsetUSS //= 1?fsubsetIl //.
  rewrite (fsubset_trans (fsetSI _ (namesm_set _ _ _))) // fsetU0.
  rewrite eval_expr_unionm // fsetIUl fsubUset fsubsetIl /=.
  rewrite (fsubset_trans (fsubsetIl _ _)) //.
  by rewrite (fsubset_trans (eval_expr_names _ _ _)) // fsubsetxx.
- (* Load *)
  rewrite fsubU1set=> /andP [Px sub] disl dish.
  rewrite eval_expr_unionm //.
  case eval_e: eval_expr=> [| |p|] //.
  rewrite unionmE; case get_p: (h1 p)=> [v|] /=.
    move=> [<- <-]; rewrite setm_union; do 3!eexists; eauto.
      by rewrite domm_set; apply/fdisjointP=> x' /fsetU1P [->|];
      move/fdisjointP: disl; apply.
    rewrite fsetIUl /= fsubUset; apply/andP; split.
      apply: (fsubset_trans (fsubsetIl _ _)).
      apply: (fsubset_trans (namesm_set _ _ _)).
      rewrite fsetU0 fsetUSS // ?fsubsetxx //=.
      apply/fsubsetP=> n Pn; apply/namesmP.
      by eapply PMFreeNamesVal; eauto.
    by apply: fsubIset; rewrite fsubsetUr.
  move: (eval_expr_names safe ls1 e); rewrite eval_e namesvE fsub1set=> Pp.
  move/fdisjointP/(_ p.1): dish; rewrite in_fsetU /= Pp /= => /(_ erefl).
  case get_p': (h2 p) => [v|] //= /namesfsPn/(_ p).
  by rewrite mem_domm get_p'=> /(_ erefl); rewrite in_fsetU in_fset1 eqxx.
- (* Store *)
  rewrite fsubUset=> /andP [sub1 sub2] disl dish.
  rewrite !eval_expr_unionm //.
  case eval_e: eval_expr=> [| |p| ] //.
  rewrite /updm unionmE setm_union.
  case get_p: (h1 p)=> [v|] //=.
    move=> [<- <-]; do 3!eexists; eauto.
    apply: (fsubset_trans (fsubsetIl _ _)).
    rewrite fsubUset; apply/andP; split; first by rewrite fsubsetUl.
    apply/(fsubset_trans (namesm_set _ _ _)); rewrite 2!fsubUset.
    rewrite fsubsetUr /=; apply/andP; split.
      apply/fsubsetU/orP; right; apply/fsubsetP=> i Pi /=.
      by apply/namesmP; eapply PMFreeNamesKey; eauto.
    by apply/(fsubset_trans (eval_expr_names _ _ _))/fsubsetUl.
  move: (eval_expr_names safe ls1 e); rewrite eval_e namesvE fsub1set=> Pp.
  move/fdisjointP/(_ p.1): dish; rewrite in_fsetU /= Pp /= => /(_ erefl).
  case get_p': (h2 p) => [v|] //= /namesfsPn/(_ p).
  by rewrite mem_domm get_p'=> /(_ erefl); rewrite in_fsetU in_fset1 eqxx.
- (* Alloc *)
  rewrite fsubU1set=> /andP [Px sub] disl dish; rewrite eval_expr_unionm //.
  case eval_e: eval_expr=> [|[n|]| |] //= [<- <-].
  rewrite setm_union /alloc_fun /= -lock /= init_block_unionm.
  have dis': fdisjoint (domm h1) (domm h2).
    apply/fdisjoint_names_domm/fdisjointP=> i Pi'.
    by move/fdisjointP: dish; apply; apply/fsetUP; right; apply/fsetUP; left.
  have F := (freshP (names (unionm ls1 ls2, unionm h1 h2))).
  do 3!eexists; eauto.
    by rewrite domm_set; apply/fdisjointP=> x' /fsetU1P [->|];
    move/fdisjointP: disl; apply.
  rewrite fsetIUl fsubUset; apply/andP; split=> /=.
    apply/(fsubset_trans _ (fsubsetUl _ _)).
    apply/(fsubset_trans (fsetSI _ (namesm_set _ _ _))).
    rewrite /= 2!fsetIUl 2!fsubUset fsubsetIl fset0I fsub0set /=.
    rewrite namesvE /=.
    apply/fsubsetP=> i /fsetIP [/namesnP -> {i} /= Pi].
    move: F; rewrite in_fsetU negb_or=> /andP [_] /=.
    by rewrite namesm_union_disjoint // in_fsetU negb_or Pi andbF.
  apply/fsubsetU/orP; right.
  apply/(fsubset_trans (fsetSI _ (names_init_block _ _ _)))/fsubsetP.
  move=> i /fsetIP [/fsetU1P [->|//] I].
  move: F; rewrite in_fsetU negb_or /= => /andP [_].
  by rewrite namesm_union_disjoint // in_fsetU I orbT.
- (* Free *)
  move=> sub disl dish; rewrite eval_expr_unionm //.
  case eval_e: eval_expr=> [| |p|] //=.
  have [|] := altP eqP=> // _.
  rewrite /free_fun -lock domm_curry; case: ifP=> [/imfsetP [/= p' inD Pp]|] //=.
  move: inD; rewrite mem_domm unionmE.
  have dish': fdisjoint (names (domm h1)) (names (domm h2)).
    apply/fdisjointP=> i Pi'.
    by move/fdisjointP: dish; apply; apply/fsetUP; right; apply/fsetUP; left.
  case get_p': (h1 p') => [v|] /=.
    move=> _ [<- <-]; exists ls1, (filterm (fun p'' _ => p''.1 != p.1) h1).
    split=> //.
      rewrite filterm_union; last by apply fdisjoint_names_domm.
      congr unionm; apply/eq_partmap=> p''; rewrite filtermE.
      case get_p'': (h2 p'')=> [v'|] //=.
      have [Pp'|] //= := altP eqP.
      have names_p: p.1 \in names (domm h1).
        apply/namesfsP; exists p'; first by rewrite mem_domm get_p'.
        by rewrite Pp; rewrite in_fsetU; apply/orP; left; apply/namesnP.
      move/fdisjointP: dish'=> /(_ _ names_p).
      suff ->: p.1 \in names (domm h2) by [].
      apply/namesfsP; exists p''; first by rewrite mem_domm get_p''.
      by rewrite -Pp'; rewrite in_fsetU; apply/orP; left; apply/namesnP.
    rewrite fsetIUl fsetUSS //= ?fsubsetIl //.
    by apply/(fsubset_trans (fsubsetIl _ _))/namesm_filter.
  case get_p'': (h2 p') => [v'|] //= _.
  move: (eval_expr_names safe ls1 e); rewrite eval_e namesvE.
  move=> /fsubsetP/(_ p.1); rewrite in_fset1 eqxx=> /(_ erefl) Pp'.
  rewrite fdisjointC in dish; move/fdisjointP/(_ p.1): dish.
  have h: p.1 \in names (domm h2).
    apply/namesfsP; exists p'; first by rewrite mem_domm get_p''.
    by rewrite Pp in_fsetU; apply/orP; left; apply/namesnP.
  by rewrite in_fsetU Pp' /= => /(_ h).
- (* Skip *)
  move=> _ ? ? [<- <-]; do 3!eexists; eauto; exact: fsubsetIl.
- (* Seq *)
  case eval_c1: eval_com=> [[ls'' h'']| |] //=.
  rewrite fsubUset=> /andP [sub1 sub2] disl dish eval_c2.
  have [ls1' [h1' [? ? disl' sub']]] := IH _ _ _ _ _ sub1 disl dish eval_c1.
  subst ls'' h''.
  have dish': fdisjoint (names (ls1', h1')) (names (domm h2)).
    move/eqP in dish.
    rewrite /fdisjoint -fsubset0 -dish fsubsetI fsubsetIr andbT.
    by rewrite (fsubset_trans _ sub') // fsetIS // fsubsetUl.
  have sub1': fsubset (vars_c c1) (domm (unionm ls1 ls2)).
    by rewrite domm_union (fsubset_trans sub1) // fsubsetUl.
  have sub2' : fsubset (vars_c c2) (domm ls1').
    apply/fsubsetP=> x x_in.
    move/fsubsetP/(_ x x_in): (sub2)=> sub2'.
    have: x \in domm (unionm ls1' ls2).
      by rewrite (eval_com_domm sub1' eval_c1) domm_union in_fsetU sub2'.
    move/fdisjointP/(_ _ sub2') in disl.
    by rewrite domm_union in_fsetU (negbTE disl) orbF.
  have [ls1'' [h1'' [? ? disl'' sub'']]] :=
    IH _ _ _ _ _ sub2' disl' dish' eval_c2.
  subst; do 3!eexists; eauto.
  by apply/(fsubset_trans _ sub'); rewrite fsubsetI fsubsetIr andbT.
- (* If *)
  rewrite 2!fsubUset=> /andP [/andP [sub1 sub2] sub3].
  rewrite eval_expr_unionm //.
  case eval_e: eval_expr=> [b| | |] //= disl dish eval_c.
  have [|ls1' [h1' [? ? disl' sub']]] := IH _ _ _ _ _ _ disl dish eval_c.
    by case: b {eval_e eval_c}.
  by subst ls' h'; do 3!eexists; eauto.
(* While *)
rewrite fsubUset=> /andP [sub1 sub2]; rewrite eval_expr_unionm //.
case eval_e: eval_expr=> [b| | |] //= disl dish eval_c.
have [|ls1' [h1' [? ? sub']]] := IH _ _ _ _ _ _ disl dish eval_c.
  case: (b); last by rewrite fsub0set.
  by rewrite /= fsetUC -fsetUA fsetUid fsubUset sub1.
by subst ls' h'; do 3!eexists; eauto.
Qed.

End Cast.
