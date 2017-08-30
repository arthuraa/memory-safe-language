From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype choice seq ssrnum ssrint ssralg bigop.

From CoqUtils Require Import ord fset partmap fperm nominal string.

Require Import basic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Structured.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.
Local Open Scope state_scope.

Notation locals := {partmap string -> value}.
Notation heap := {partmap ptr -> value}.

Implicit Types (ls : locals) (h : heap) (x : string) (s : locals * heap).

Fixpoint eval_com c s k : result {restr locals * heap} :=
  if k is S k' then
    match c with
    | Assn x e =>
      Done (Restr (setm s.1 x (eval_expr true e s.1), s.2))

    | Load x e =>
      if eval_expr true e s.1 is VPtr p _ then
        if s.2 p is Some v then Done (Restr (setm s.1 x v, s.2))
        else Error
      else Error

    | Store e e' =>
      if eval_expr true e s.1 is VPtr p _ then
        if updm s.2 p (eval_expr true e' s.1) is Some h' then Done (Restr (s.1, h'))
        else Error
      else Error

    | Alloc x e =>
      if eval_expr true e s.1 is VNum (Posz n) then
        Done (new (names s) (fun i =>
                Restr (setm s.1 x (VPtr (i, 0 : int) n),
                       unionm (mkblock i (nseq n (VNum 0))) s.2)))
      else Error

    | Free e =>
      if eval_expr true e s.1 is VPtr p _ then
        if p.2 == 0 then
          if p.1 \in domm ((@currym _ _ _ : heap -> _) s.2) then
            Done (Restr (s.1, filterm (fun (p' : ptr) _ => p'.1 != p.1) s.2))
          else Error
        else Error
      else Error

    | Skip => Done (Restr s)

    | Seq c1 c2 =>
      match eval_com c1 s k' with
      | Done rs' => bindr fset0 (fun s' => eval_com c2 s' k') rs'
      | Error => Error
      | NotYet => NotYet
      end

    | If e ct ce =>
      if eval_expr true e s.1 is VBool b then
        eval_com (if b then ct else ce) s k'
      else Error

    | While e c =>
      if eval_expr true e s.1 is VBool b then
        eval_com (if b then Seq c (While e c) else Skip) s k'
      else Error
    end
  else NotYet.

Global Instance eval_binop_eqvar b : {eqvar eval_binop b}.
Proof.
by case: b => [] π [b1|n1|p1 sz1|] _ <- [b2|n2|p2 sz2|] _ <- //=; finsupp.
Qed.

Global Instance eval_expr_eqvar e : {eqvar eval_expr true e}.
Proof.
move=> π ls _ <-; elim: e=> [x|b|n|b e1 IH1 e2 IH2|e IH| |e IH|e IH|e IH] //=.
- rewrite renamemE /= renameT.
  by case: (ls x)=> [v|] //=.
- by rewrite -IH1 -IH2; apply: eval_binop_eqvar.
- by rewrite -IH; case: eval_expr.
- by rewrite -IH; case: eval_expr.
by rewrite -IH; case: eval_expr.
Qed.

Global Instance match_value_eqvar
  T {eT : nominalRel T}
  π v1 v2 b11 b12 b21 b22 b31 b32 b41 b42 :
  nomR π v1 v2 ->
  nomR π b11 b12 ->
  nomR π b21 b22 ->
  nomR π b31 b32 ->
  nomR π b41 b42 ->
  nomR π
       match v1 with
       | VBool x => b11 x : T
       | VNum x => b21 x
       | VPtr x sz => b31 x sz
       | VNil => b41
       end
       match v2 with
       | VBool x => b12 x : T
       | VNum x => b22 x
       | VPtr x sz => b32 x sz
       | VNil => b42
       end.
Proof. by move=> <- ????; case: v1=> * /=; finsupp. Qed.

Global Instance match_int_eqvar
  T {eT : nominalRel T}
  π n1 n2 b11 b12 b21 b22 :
  nomR π n1 n2 ->
  nomR π b11 b12 ->
  nomR π b21 b22 ->
  nomR π
       match n1 with
       | Posz x => b11 x : T
       | Negz x => b21 x
       end
       match n2 with
       | Posz x => b12 x : T
       | Negz x => b22 x
       end.
Proof. by move=> <- ? ?; case: n1=> // n; finsupp. Qed.

Global Instance match_result_eqvar
  (T : nominalType) S {eS : nominalRel S}
  π (r1 r2 : result T) b11 b12 b21 b22 b31 b32 :
  nomR π r1 r2 ->
  nomR π b11 b12 ->
  nomR π b21 b22 ->
  nomR π b31 b32 ->
  nomR π
       match r1 with
       | Done x => b11 x : S
       | Error => b21
       | NotYet => b31
       end
       match r2 with
       | Done x => b12 x : S
       | Error => b22
       | NotYet => b32
       end.
Proof. case: r1 => [?| |] // <-; finsupp. Qed.

(*

(* Trying to figure out the problem with unification *)

Inductive some_prop (T : eqType) := SomeProp.

Class foo (T : eqType) := foo_proof : some_prop T.

Instance foo_inst (T : choiceType) : foo T := SomeProp T.

Record bar := Bar {
  bar_sort :> eqType;
  _ : some_prop bar_sort
}.

Lemma bar_proof (B : bar) : some_prop B.
Proof. by case: B. Qed.

Definition bar_inst (T : choiceType) := @Bar T (SomeProp T).
Canonical bar_inst.

Lemma test_nat_eqType : some_prop nat_eqType.
Proof.
(* eapply bar_proof. *) (* Does not work (Unable to unify) *)
(* apply: foo_proof. *) (* Does work *)
(* apply: bar_proof. *) (* Does not work (Cannot apply lemma) *)
eapply foo_proof. (* Does work *)
Qed.

Lemma test_prod_eqType : some_prop (prod_eqType nat_eqType nat_eqType).
(* eapply bar_proof. *) (* Does not work (Unable to unify) *)
(* apply: foo_proof. *) (* Does not work (Could not fill dependent hole in apply) *)
(* apply: bar_proof. *) (* Does not work (Cannot apply lemma ) *)
eapply foo_proof. (* Application works, but cannot infer the instance of foo by itself *)
Abort.

Canonical my_choice := Eval hnf in [choiceType of prod_eqType nat_eqType nat_eqType].

Lemma test_prod_with_canonical : some_prop (prod_eqType nat_eqType nat_eqType).
(* eapply bar_proof. *) (* Does not work (Unable to unify) *)
(* apply: foo_proof. *) (* Does not work (Could not fill dependent hole in apply) *)
(* apply: bar_proof. *) (* Does not work (Cannot apply lemma ) *)
eapply foo_proof. (* Application works, but cannot infer the instance of foo by itself *)
Abort.

*)

Hint Extern 4 (@nomR ?S ?cS ?π (?f1 ?x1) (?f2 ?x2)) =>
  let T  := type of x1 in
  let cT := constr:(_ : nominalRel T) in
  eapply (@nomR_app T S cT cS π f1 f2 x1 x2) : typeclass_instances.

Global Instance eval_com_eqvar : {eqvar eval_com}.
Proof.
move=> π c1 c2 c1c2 s1 s2 s1s2 k _ <-; rewrite renameT.
elim: k π c1 c2 c1c2 s1 s2 s1s2 => [|k IH] π c _ <- s1 s2 s1s2 //=.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] /=; by finsupp.
Qed.

(* FIXME: This lemma has a simpler proof in basic.v *)
Lemma eval_com_vars s rs' c k :
  fsubset (vars_c c) (domm s.1) ->
  eval_com c s k = Done rs' ->
  expose (mapr fset0 (fun s' => domm s'.1) rs') = domm s.1.
Proof.
elim: k s rs' c => [|k IH] /= [ls h] rs'; first by [].
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] /=;
rewrite ?fsubU1set ?fsubUset.
- case/andP=> [Px Pe] [<-]; rewrite maprE0 exposeE0 domm_set /=.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsubsetUr.
- case/andP=> [Px Pe].
  case: eval_expr => // p sz; case: (h p)=> [v|] //= [<-] {rs'}.
  rewrite maprE0 exposeE0 domm_set.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsubsetUr.
- case/andP=> Pe Pe'.
  case: eval_expr => // p sz; rewrite /updm; case: (h p)=> [v|] //= [<-] {rs'}.
  by rewrite maprE0 exposeE0 /=.
- case: eval_expr => [|[n|]| |] // /andP [Px Pe] [<-].
  rewrite namespE /= (newE _ (freshP _)) maprE ?fdisjoints1 ?in_fset0 //.
  rewrite domm_set exposeE.
  apply/eqP; rewrite eqEfsubset; apply/andP; split; last exact: fsubsetUr.
  by rewrite fsubUset fsubsetxx andbT fsub1set.
- case: eval_expr => // p sz.
  have [|]:= altP eqP=> // _; case: ifP=> //= in_h1 sub [<-] {rs'}.
  by rewrite maprE0 exposeE0.
- by move=> _ [<-] {rs'}; rewrite maprE0 exposeE0.
- case/andP=> vars_c1 vars_c2.
  case ev_c1: (eval_com _ _ _) => [rs''| |] //=.
  case/(restrP (names (ls, h))): rs'' ev_c1 => A [/= ls' h'] dis sub ev_c1.
  move: (IH (ls, h) _ _ vars_c1 ev_c1).
  rewrite /= bindrE ?maprE ?exposeE ?fdisjoint0s //= => e_ls.
  case ev_c2: eval_com=> [rs''| |] //= [<-] {rs'}; rewrite -e_ls /= in vars_c2.
  by rewrite -hide_mapr ?fdisjoint0s // hideT (IH (ls', h') _ c2) //=.
- case: eval_expr=> // - b.
  by rewrite -andbA => /and3P [_ vars_c1 vars_c2]; case: b; eapply IH; eauto.
case: eval_expr=> // - [] P; apply: IH; try by rewrite fsub0set.
by rewrite /= fsetUC -fsetUA fsetUid fsubUset.
Qed.

Lemma eval_com_blocks s rs' c k :
  eval_com c s k = Done rs' ->
  elimr (names s)
        (fun A s' => fsubset (names (domm s'.2))
                             (names (domm s.2) :|: A)) rs'.
Proof.
elim: k s rs' c => [|k IH] /= [ls h] rs' //.
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] /=.
- by move=> [<-] {rs'}; rewrite elimrE0 fsetU0 fsubsetxx.
- case: eval_expr=> //= p sz; case: getm=> //= v [<-] {rs'}.
  by rewrite elimrE0 fsetU0 fsubsetxx.
- case: eval_expr=> //= p sz; rewrite /updm.
  case get_p: getm=> [v|] //= [<-] {rs'}.
  rewrite elimrE0 fsetU0 domm_set namesfsU fsubUset fsubsetxx andbT.
  rewrite namesfsE /= big_seq1 namespE namesnE fsetU0 fsub1set.
  apply/namesfsP; exists p; first by apply/dommP; eauto.
  by rewrite namespE fsetU0 in_fset1 eqxx.
- case: eval_expr=> [| [n|] | |] //= [<-] {rs'}.
  move: (fresh _) (freshP (names (ls, h)))=> i nin_i.
  rewrite (newE _ nin_i) elimrE ?fdisjoints1 ?domm_union ?namesfsU //=.
    rewrite fsetUC fsetUS // names_domm_mkblock fun_if if_arg fsub0set.
    by rewrite fsubsetxx if_same.
  rewrite fsub1set; apply/fsetUP; left=> /=.
  have ? : setm ls x (VPtr (i, 0 : int) n) x = Some (VPtr (i, 0 : int) n).
    by rewrite setmE eqxx.
  apply/namesmP/@PMFreeNamesVal; eauto.
  by rewrite namesvE in_fset1 eqxx.
- case: eval_expr=> //= p sz; case: ifP=> //= _; case: ifP=> //= _ [<-] {rs'}.
  by rewrite elimrE0 fsetU0 /= namesfs_subset // domm_filter.
- by move=> [<-] {rs'}; rewrite elimrE0 /= fsetU0 fsubsetxx.
- (* FIXME: This is way too complicated *)
  case ev_c1: eval_com=> [rs''| |] //=.
  case/(restrP (names (ls, h))): rs'' ev_c1=> /= A s' dis sub ev_c1.
  rewrite bindrE ?fdisjoint0s //.
  case ev_c2: eval_com=> [rs''| |] //= [<-] {rs'}.
  case/(restrP (names (ls, h) :|: names s')): rs'' ev_c2=> /= A' s'' dis' sub' ev_c2.
  move: dis'; rewrite fdisjointUl=> /andP [dis_s_A' dis_s'_A'].
  rewrite hideU hideI namesrE fsetIUl (fsetIidPl _ _ sub').
  rewrite elimrE ?namesT ?fdisjoint0s ?fdisjointUr ?dis ?fsubUset
          ?sub' ?andbT ?fsubsetIr //=.
    move: (IH _ _ _ ev_c1); rewrite elimrE ?namesT ?fdisjoint0s //= => sub1.
    suffices sub'' : fsubset (names (domm s''.2)) (names (domm h) :|: (A :|: A')).
      apply/fsubsetP=> i i_in_s''; rewrite in_fsetU in_fsetU in_fsetI.
      rewrite namespE in_fsetU [_ \in names s''.2]in_fsetU i_in_s'' /= orbT andbT.
      by move/fsubsetP/(_ _ i_in_s''): sub''; rewrite 2!in_fsetU.
    apply: fsubset_trans; last by rewrite fsetUA; exact: fsetSU sub1.
    by move: (IH _ _ _ ev_c2); rewrite elimrE ?namesT ?fdisjoint0s.
  rewrite dis_s_A' andbT fdisjointC; apply: fdisjoint_trans.
     exact: fsubsetIl.
   by rewrite fdisjointC.
- by case: eval_expr=> // b; apply: IH.
- by case: eval_expr=> // b; apply: IH.
Qed.

Lemma frame_ok c s1 s2 k rs :
  fsubset (vars_c c) (domm s1.1) ->
  fdisjoint (names (domm s1.2)) (names (domm s2.2)) ->
  eval_com c s1 k = Done rs ->
  eval_com c (s1 ∪ s2) k =
  Done (mapr (names s2) (stateu ^~ s2) rs).
Proof.
elim: k c s1 rs => [|k IH] //= c s1 rs.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] /=;
rewrite ?fsubUset ?fsub1set.
- case/andP=> [x_in_vs sub] dis [<-] {rs}.
  by rewrite maprE0 eval_expr_unionm // setm_union.
- case/andP=> [x_in_vs sub] dis.
  rewrite eval_expr_unionm //; case: eval_expr=> //= p sz.
  rewrite unionmE; case get_p: getm=> [v|] //= [<-] {rs}.
  by rewrite maprE0 setm_union.
- case/andP=> [sub1 sub'] dis.
  rewrite !eval_expr_unionm //; case: eval_expr=> //= p sz.
  rewrite /updm unionmE; case: getm=> //= _ [<-] {rs}.
  by rewrite maprE0 setm_union.
- case/andP=> [x_in_vs sub] dis.
  rewrite eval_expr_unionm //; case: eval_expr=> [|[n|]| |] //= [<-] {rs}.
  move: (fresh _) (freshP (names s1 :|: names s2)) => i.
  rewrite in_fsetU !negb_or=> /andP [i1 i2].
  rewrite [in RHS](@newE _ _ _ i) //.
  (* FIXME: This massaging should not be necessary *)
  rewrite namespE /=.
  move els: (unionm s1.1 s2.1) => ls; move eh: (unionm s1.2 s2.2)=> h.
  rewrite [in LHS](@newE _ _ _ i) -?{}els -?{}eh.
    by rewrite maprE ?setm_union ?unionmA // fdisjoints1.
  have: fsubset (names (s1 ∪ s2)) (names s1 :|: names s2).
    eapply nom_finsuppP; finsupp.
  by move=> /fsubsetP/(_ i)/contra; apply; rewrite in_fsetU negb_or i1.
- move=> sub dis.
  rewrite !eval_expr_unionm //; case: eval_expr=> //= p sz.
  case: ifP=> //= _; rewrite !domm_curry domm_union imfsetU in_fsetU.
  case: ifP=> //= /imfsetP [p' in_h1 e_p] [<-] {rs}.
  rewrite maprE0 filterm_union ?fdisjoint_names_domm // (_ : filterm _ s2.2 = s2.2) //.
  have {p' e_p in_h1} in_h1 : p.1 \in names (domm s1.2).
    by apply/namesfsP; exists p'=> //; rewrite e_p in_fsetU namesnE in_fset1 eqxx.
  apply/eq_partmap=> p'; rewrite filtermE.
  case get: (s2.2 p')=> [v|] //=.
  have [e_p|] //= := altP (_ =P _).
  suffices in_h2 : p.1 \in names (domm s2.2).
    by move/fdisjointP/(_ _ in_h1): dis; rewrite in_h2.
  apply/namesfsP; exists p'; first by apply/dommP; eauto.
  by rewrite -e_p in_fsetU namesnE in_fset1 eqxx.
- by move=> _ dis [<-] {rs}; rewrite maprE0.
- case/andP=> [sub1 sub2] dis.
  case ev_c1: eval_com => [rs1| |] //=.
  case/(restrP (names s1 :|: names s2)):
    rs1 ev_c1 => /= [A s' dis' sub] ev_c1.
  move: dis'; rewrite fdisjointUl => /andP [dis1 dis2].
  rewrite bindrE ?fdisjoint0s ?(IH _ _ (hide A (Restr s'))) //.
  case ev_c2: eval_com => [rs2| |] //= [<-] {rs}.
  rewrite maprE // bindrE ?fdisjoint0s //=.
  rewrite (IH _ _ rs2) //= -?hide_mapr //.
    move: (@eval_com_vars s1 _ _ _ sub1 ev_c1).
    by rewrite /= maprE ?fdisjoint0s ?exposeE // => ->.
  move: (@eval_com_blocks s1 _ _ _ ev_c1).
  rewrite elimrE ?namesT ?fdisjoint0s //=.
  move => sub_blocks; apply: fdisjoint_trans; first exact: sub_blocks.
  have ?: fsubset (names (domm s2.2)) (names s2.2) by exact: fsubsetUl.
  rewrite fdisjointUl dis /= fdisjointC; apply: fdisjoint_trans.
    by eauto.
  by move: dis2; rewrite fdisjointUl => /andP [].
- rewrite -andbA=> /and3P [sub_e sub_c1 sub_c2] dis_h1h2.
  rewrite eval_expr_unionm //; case: eval_expr=> //= b ev_if.
  by rewrite (IH _ _ rs) //; case: (b).
case/andP=> [sub_e sub_c] dis_h1h2.
rewrite eval_expr_unionm //; case: eval_expr=> //= b ev_if.
rewrite (IH _ _ rs) //; case: (b)=> //=; rewrite ?fsub0set //.
by rewrite !fsubUset sub_c sub_e.
Qed.

Lemma frame_loop c s1 s2 k :
  fsubset (vars_c c) (domm s1.1) ->
  fdisjoint (names (domm s1.2)) (names (domm s2.2)) ->
  eval_com c s1 k = NotYet ->
  eval_com c (s1 ∪ s2) k = NotYet.
Proof.
elim: k c s1 => [|k IH] //= c s1.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=;
rewrite ?fsubUset ?fsub1set.
- by case: eval_expr=> //= p; case: getm.
- by case: eval_expr=> //= p; case: updm.
- by case: eval_expr=> [|[n|]| |].
- by case: eval_expr=> //= p; do 2![case: ifP=> //= _].
- case/andP=> [c1_ls1 c2_ls2] dis_h1_h2.
  case ev_c1: eval_com=> [rs'| |] //=; last by rewrite IH.
  case/(restrP (names s1 :|: names s2)): rs' ev_c1
    => /= A s1' disA subA ev_c1.
  move: disA; rewrite fdisjointUl=> /andP [disA1 disA2].
  rewrite bindrE ?fdisjoint0s // (frame_ok _ _ ev_c1) //.
  rewrite maprE ?bindrE ?fdisjoint0s //.
  case ev_c2: eval_com=> //= _; rewrite IH //.
    move: (eval_com_vars c1_ls1 ev_c1)=> /=.
    by rewrite maprE ?fdisjoint0s ?exposeE // => ->.
  move: (eval_com_blocks ev_c1).
  rewrite elimrE ?namesT ?fdisjoint0s //= => sub_h1'_h1A.
  apply: fdisjoint_trans; first exact: sub_h1'_h1A.
  rewrite fdisjointUl dis_h1_h2 fdisjointC /=.
  move: disA2; rewrite fdisjointUl=> /andP [_].
  by rewrite fdisjointUl=> /andP [].
- rewrite -andbA => /and3P [e_ls1 c1_ls1 c2_ls2] dis_h1_h2.
  rewrite eval_expr_unionm //=; case: eval_expr=> //= b ev_if.
  by rewrite IH //; case: (b).
case/andP=> [e_ls1 c_ls1] dis_h1_h2; rewrite eval_expr_unionm //.
case: eval_expr=> //= b ev_while.
by rewrite IH //; case: (b)=> //=; rewrite ?fsub0set // !fsubUset e_ls1 c_ls1.
Qed.

Lemma get_mem_dis e s1 h2 p sz :
  fdisjoint (names s1) (names (domm h2)) ->
  eval_expr true e s1.1 = VPtr p sz ->
  h2 p = None.
Proof.
move=> dis eval_e; case get_p: (h2 p)=> [v|] //.
move: (eval_expr_names true s1.1 e); rewrite eval_e namesvE.
have inNh2: p.1 \in names (domm h2).
  apply/namesfsP; exists p; first by rewrite mem_domm get_p.
  by apply/fsetUP; left; apply/namesnP.
rewrite fsub1set=> inNls1.
have inNs1: p.1 \in names s1 by rewrite in_fsetU inNls1.
by move/fdisjointP/(_ _ inNs1): dis; rewrite inNh2.
Qed.

Lemma frame_error c s1 s2 k :
  fsubset (vars_c c) (domm s1.1) ->
  fdisjoint (names s1) (names (domm s2.2)) ->
  eval_com c s1 k = Error ->
  eval_com c (s1 ∪ s2) k = Error.
Proof.
elim: k c s1 => [|k IH] //= c s1.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=;
rewrite ?fsubUset ?fsub1set.
- case/andP=> [x_ls1 e_ls1] dis_s1_h2.
  rewrite eval_expr_unionm //; case ev_e: eval_expr=> [| |p|] //=.
  by rewrite unionmE (get_mem_dis dis_s1_h2 ev_e); case: getm.
- case/andP=> [e_ls1 e'_ls1] dis_s1_h2.
  rewrite eval_expr_unionm //; case ev_e: eval_expr=> [| |p|] //=.
  rewrite /updm unionmE (get_mem_dis dis_s1_h2 ev_e).
  by case: getm.
- case/andP=> [x_ls1 e_ls1] dis_s1_h2.
  by rewrite eval_expr_unionm //; case ev_e: eval_expr=> [|[n|]| |] //=.
- move=> e_ls1 dis_s1_h2.
  rewrite eval_expr_unionm //; case ev_e: eval_expr=> [| |p|] //=.
  case: ifP=> //= _; rewrite !domm_curry domm_union imfsetU in_fsetU.
  case: ifP=> //= _ _; case: ifP=> //= /imfsetP /= [p' in_h2 e_p].
  move: (eval_expr_names true s1.1 e); rewrite ev_e namesvE fsub1set.
  move=> in_ls1; have in_Nh2 : p'.1 \in names (domm s2.2).
    apply/namesfsP; exists p'=> //.
    by rewrite in_fsetU namesnE in_fset1 eqxx.
  move: dis_s1_h2; rewrite fdisjointC=> /fdisjointP/(_ _ in_Nh2).
  by rewrite in_fsetU /= -e_p in_ls1.
- case/andP=> [c1_ls1 c2_ls2] dis_s1_h2.
  case ev_c1: eval_com=> [rs'| |] //=; last by rewrite IH.
  rewrite (@frame_ok _ _ _ _ rs') //.
    case/(restrP (names s1 :|: names s2)): rs' ev_c1=> /= A s1' dis' sub.
    move: dis'; rewrite fdisjointUl=> /andP [dis_s1_A dis_s2_A].
    rewrite maprE ?bindrE ?fdisjoint0s //= => ev_c1.
    case ev_c2: eval_com=> //=; rewrite IH //.
      move: (eval_com_vars c1_ls1 ev_c1).
      by rewrite maprE ?fdisjoint0s ?exposeE //= => ->.
    have: fsubset (names (eval_com c1 s1 k)) (names s1).
      by eapply nom_finsuppP; finsupp.
    rewrite ev_c1 namesresE names_hider namesrE fsubDset => sub_s1'.
    apply: fdisjoint_trans; first by eauto.
    rewrite fdisjointUl dis_s1_h2 andbT fdisjointC.
    apply: fdisjoint_trans; last by exact: dis_s2_A.
    by eapply nom_finsuppP; finsupp.
  apply: fdisjoint_trans; last by exact: dis_s1_h2.
  by rewrite namespE /=; eapply nom_finsuppP; finsupp.
- case/andP=> [/andP [e_ls1 c1_ls1] c2_ls2] dis_s1_h2.
  rewrite eval_expr_unionm //; case: eval_expr=> //= b ev_if.
  by rewrite IH //; case: (b).
case/andP=> [e_ls1 c_ls1] dis_s1_h2.
rewrite eval_expr_unionm //; case: eval_expr=> //= b ev_if.
by rewrite IH // !fun_if if_arg /= !fsubUset c_ls1 e_ls1 fsub0set if_same.
Qed.

Corollary noninterference s1 s21 rs' s22 c k :
  fsubset (vars_c c) (domm s1.1) ->
  fdisjoint (names s1) (names (domm s21.2)) ->
  fdisjoint (names (domm s1.2)) (names (domm s22.2)) ->
  eval_com c (s1 ∪ s21) k = Done rs' ->
  exists rs1',
    [/\ eval_com c s1 k = Done rs1',
        rs' = mapr (names s21) (stateu ^~ s21) rs1' &
        eval_com c (s1 ∪ s22) k =
        Done (mapr (names s22) (stateu ^~ s22) rs1')].
Proof.
move=> sub dis1 dis2 eval_c.
case eval_c': (eval_com c s1 k) => [rs1'| |] //=.
- exists rs1'; split; eauto.
    move: eval_c; rewrite (frame_ok sub _ eval_c') => [[<-]//|] /=.
    apply/(fdisjoint_trans _ dis1); eapply nom_finsuppP; finsupp.
  by apply: frame_ok=> //.
- by rewrite (frame_error sub dis1 eval_c') in eval_c.
rewrite (frame_loop sub _ eval_c') // in eval_c.
apply/(fdisjoint_trans _ dis1); eapply nom_finsuppP; finsupp.
Qed.

Lemma eval_basic_restr c s k :
  exists A,
    eval_com c s k =
    match basic.eval_com true c s k with
    | Done s' => Done (hide A (Restr s'))
    | Error => Error
    | NotYet => NotYet
    end.
Proof.
elim: k s c => /= [|k IH] s c; first by exists fset0.
case: c => [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=.
- by exists fset0; rewrite hide0.
- exists fset0; case: eval_expr=> //= p; case: getm=> //= v.
  by rewrite hide0.
- exists fset0.
  by case: eval_expr=> //= p; case: updm=> //= h'; rewrite hide0.
- exists (fset1 (fresh (names s))).
  by case: eval_expr=> [|[n|] | |] //=.
- exists fset0.
  case: eval_expr=> //= p; case: ifP=> //= _.
  by case: ifP=> //= _; rewrite hide0.
- by exists fset0; rewrite hide0.
- have [A ->] := IH s c1.
  case: basic.eval_com => [s'| |]; eauto.
  have [A' e] := IH s' c2.
  exists (A :|: A'); rewrite bindrE ?fdisjoint0s // e.
  by case: basic.eval_com=> //= s''; rewrite -hideU.
- case: eval_expr; try by exists fset0.
  by case; apply: IH.
case: eval_expr; try by exists fset0.
by case; apply: IH.
Qed.

Lemma mod_vars_cP s rs' c x k :
  eval_com c s k = Done rs' ->
  x \notin mod_vars_c c ->
  mapr fset0 (fun s => s.1 x) rs' = Restr (s.1 x).
Proof.
elim: k s c rs' => /= [|k IH] s c rs' //.
case: c => [x' e|x' e|e e'|x' e|e| |c1 c2|e c1 c2|e c] //=;
rewrite ?in_fset1.
- by move=> [<-]; rewrite maprE0 //= setmE => /negbTE ->.
- case: eval_expr=> //= p sz; case: getm=> //= v [<-].
  by rewrite maprE0 //= setmE => /negbTE ->.
- case: eval_expr=> //= p sz; case: updm=> //= h' [<-].
  by rewrite maprE0 //= setmE.
- case: eval_expr=> [|[n|]| |] //= [<-].
  rewrite /new; move: (fresh _) (freshP (names s)) => i nin_i.
  rewrite !maprE ?fdisjoint0s //= setmE => /negbTE ->.
  rewrite hideD // namesrE fdisjointC; apply: (@fdisjoint_trans _ _ (names s)).
    eapply nom_finsuppP; finsupp.
  by rewrite fdisjoints1.
- case: eval_expr=> // p sz; case: ifP => // _; case: ifP=> // _ [<-].
  by rewrite maprE0.
- by move=> [<-] _; rewrite maprE0.
- case ev1: eval_com=> [rs''| |] //=.
  case/(restrP fset0): rs'' ev1 => /= A s'' _ sub ev1.
  rewrite bindrE ?fdisjoint0s //.
  case ev2: eval_com=> [rs''| |] // [<-] {rs'}.
  rewrite in_fsetU => /norP [nin1 nin2].
  rewrite -hide_mapr ?fdisjoint0s // (IH _ _ _ ev2 nin2).
  by rewrite -(IH _ _ _ ev1 nin1) maprE ?fdisjoint0s.
- rewrite in_fsetU; case: eval_expr=> // b ev /norP [nin1 nin2].
  by apply: IH; eauto; case: (b).
- case: eval_expr=> // b ev nin.
  apply: IH; eauto.
  by case: (b); rewrite ?in_fset0 //= fsetUid.
Qed.

End Structured.
